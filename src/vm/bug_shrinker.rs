use std::{cmp, fmt::Display, mem, panic};

use super::{
    run_state, ActualTracer, BlockInterpretResult, NoStats, OperationError, Optimizer, OptimizedBlock,
    OptimizingVM, State, VMOptions,
};
use crate::compiler::{
    cfg::GraphBuilder,
    osmibytecode::OsmibytecodeBlock,
    osmibytecode_vm::RegFile,
    precompiler::{NoTrace, Precompiler, TraceProvider},
};

const STACK_PREVIEW: usize = 16;

pub fn verify_block<'prog, 'opts>(
    vm: &OptimizingVM,
    rev: bool, ip: usize,
    start_state: State<'prog, Optimizer>,
    options: &VMOptions<'opts>,
) -> (Result<BlockInterpretResult, OperationError>, State<'prog, Optimizer>) {

    let (optimizer, start_state) = start_state.swap_tracer(NoStats::default());
    let block = optimizer.get_block(rev, ip).unwrap();
    let (optimized_stack, optimized_result) = panic::catch_unwind(|| {
        let mut optimized_stack = start_state.stack.clone();
        let mut tmp_regs = RegFile::new_debug();
        let r = OptimizingVM::interpret_block(block, &mut optimized_stack, &mut tmp_regs, vm.conf.error_as_deopt).expect("errors not used atm");
        (optimized_stack, r)
    }).unwrap_or_else(|err| {
        println!("{}", format_panic_message("Optimized block", err));
        run_shrinker(vm, options, start_state.clone(), None, None);
    });

    let mut reference_state = start_state.clone();
    let mut reference_options = options.clone();
    reference_options.stop_after = start_state.instructions_run + optimized_result.executed_ksplang;
    run_state(&mut reference_state, &reference_options)
        .expect("Real program failed while optimized program ran fine :|");

    if optimized_stack == reference_state.stack && optimized_result.next_ip == reference_state.ip {
        let mut state = start_state.swap_tracer(optimizer).1;
        state.stack = optimized_stack;
        return (Ok(optimized_result), state);
    }

    // TODO: write full repro to a file

    println!("exectution result mismatch detected at ip {} {}", start_state.ip, start_state.reversed);
    println!("  optimized next_ip={} stack={}",
        optimized_result.next_ip,
        format_stack_preview(&optimized_stack)
    );
    println!("  reference next_ip={} stack={}",
        reference_state.ip,
        format_stack_preview(&reference_state.stack)
    );

    run_shrinker(
        vm,
        options,
        start_state,
        Some((&optimized_stack, optimized_result.next_ip)),
        Some((&reference_state.stack, reference_state.ip)),
    );
}

fn run_shrinker<'prog, 'opts>(
    vm: &OptimizingVM,
    options: &VMOptions<'opts>,
    start_state: State<'prog, NoStats>,
    initial_mismatch: Option<(&[i64], usize)>,
    initial_baseline: Option<(&[i64], usize)>,
) -> ! {
    let mut ctx = ShrinkingContext::new(vm, options.clone(), start_state);
    let (settings, outcome) = ctx.find_reproducing_settings();
    println!("Identified repro settings: {settings:?}. Now shrinking the settings.");
    // TODO: write repro with settings to file
    let (settings, outcome) = ctx.shrink_settings(settings, outcome);
    ctx.shrink_from_front(&settings, cmp::max(outcome.executed_ksplang, settings.interpret_limit as u64));
    let (settings, outcome) = ctx.shrink_settings(settings, outcome);
    ctx.panic_with_summary(
        &settings,
        &outcome,
        initial_mismatch,
        initial_baseline,
    );
}

#[derive(Clone, Debug)]
struct CompileSettings {
    use_trace: bool,
    use_osmibyte: bool,
    soft_limits: bool,
    bb_limit: usize,
    instr_limit: usize,
    interpret_limit: usize,
    override_verbosity: Option<u8>,
}

struct ShrinkingContext<'vm, 'prog, 'opts> {
    vm: &'vm OptimizingVM,
    options: VMOptions<'opts>,
    start_state: State<'prog, NoStats>,
}

#[derive(Clone, Debug)]
struct ReproOutcome {
    executed_ksplang: u64,
    kind: OutcomeKind,
}

impl Display for ReproOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: ", self.executed_ksplang)?;
         match &self.kind {
            OutcomeKind::Works => write!(f, "works")?,
            OutcomeKind::Error(err) => {
                let chars = err.find('\n').unwrap_or(err.len()).min(100);
                let chars = err.floor_char_boundary(chars);
                write!(f, "Failed: {}", &err[..chars])?
            },
            OutcomeKind::OpError(err) => {
                write!(f, "Returned error: {err}")?
            },
            OutcomeKind::Mismatch { optimized_stack, optimized_ip, reference_stack, reference_ip } => {
                if optimized_stack == reference_stack {
                    write!(f, "IP mismatch ({} != {})", reference_ip, optimized_ip)?;
                } else if reference_ip != optimized_ip {
                    write!(f, "Stack + IP mismatch ({} != {})", reference_ip, optimized_ip)?;
                } else if reference_stack.len() != optimized_stack.len() {
                    write!(f, "Stack len mismatch ({} != {})", reference_stack.len(), optimized_stack.len())?;
                } else {
                    let mismatch_ix = (0..reference_stack.len()).rev().position(|ix| reference_stack.get(ix) != optimized_stack.get(ix)).unwrap();
                    write!(f, "Stack mismatch (at [{mismatch_ix} / {}]: {} != {})",
                              mismatch_ix as i64 - reference_stack.len() as i64,
                              reference_stack[reference_stack.len() - mismatch_ix - 1], optimized_stack[reference_stack.len() - mismatch_ix - 1])?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum OutcomeKind {
    Works,
    Mismatch {
        optimized_stack: Vec<i64>,
        optimized_ip: usize,
        reference_stack: Vec<i64>,
        reference_ip: usize,
    },
    Error(String),
    OpError(OperationError),
}

impl<'vm, 'prog, 'opts> ShrinkingContext<'vm, 'prog, 'opts> {
    fn new(
        vm: &'vm OptimizingVM,
        options: VMOptions<'opts>,
        start_state: State<'prog, NoStats>,
    ) -> Self {
        Self { vm, options, start_state }
    }

    fn default_config(&self) -> CompileSettings {
        CompileSettings {
            use_trace: false,
            use_osmibyte: self.vm.conf.allow_osmibyte_backend,
            bb_limit: self.vm.conf.adhoc_branch_limit as usize,
            instr_limit: self.vm.conf.adhoc_instr_limit as usize,
            interpret_limit: self.vm.conf.adhoc_interpret_limit as usize,
            soft_limits: false, // TODO Maybe try true if we hit reproducibility problems?
            override_verbosity: Some(0)
        }
    }

    fn find_reproducing_settings(&mut self) -> (CompileSettings, ReproOutcome) {
        let base = self.default_config();
        let osmibyte_options: &[bool] = if base.use_osmibyte { &[false, true] } else { &[false] };
        for &use_osmibyte in osmibyte_options {
            for use_trace in [false, true] {
                let mut settings = base.clone();
                settings.use_trace = use_trace;
                settings.use_osmibyte = use_osmibyte;
                let outcome = self.compile_and_reproduce(&settings);
                if outcome.kind != OutcomeKind::Works {
                    return (settings, outcome);
                }
            }
        }
        panic!("shrinker: unable to reproduce mismatch with any strategy");
    }

    fn shrink_settings(&mut self, mut settings: CompileSettings, mut outcome: ReproOutcome) -> (CompileSettings, ReproOutcome) {
        self.shrink_limit(
            "bb_limit",
            &mut settings,
            &mut outcome,
            |s| s.bb_limit,
            |s, value| s.bb_limit = value,
        );
        self.shrink_limit(
            "instr_limit",
            &mut settings,
            &mut outcome,
            |s| s.instr_limit,
            |s, value| s.instr_limit = value,
        );
        self.shrink_limit(
            "interpret_limit",
            &mut settings,
            &mut outcome,
            |s| s.interpret_limit,
            |s, value| s.interpret_limit = value,
        );
        (settings, outcome)
    }

    fn shrink_limit<FGet, FSet>(
        &mut self,
        label: &str,
        settings: &mut CompileSettings,
        outcome: &mut ReproOutcome,
        get: FGet,
        set: FSet,
    ) -> usize
    where
        FGet: Fn(&CompileSettings) -> usize,
        FSet: Fn(&mut CompileSettings, usize),
    {
        let mut broken = get(settings);
        let mut works = 0;
        let mut min_broken = broken;
        while broken.saturating_sub(works) > 1 {
            let mid = (broken + works) / 2;
            set(settings, mid);
            if mid == 0 || mid == broken {
                break;
            }
            let new_outcome = self.compile_and_reproduce(settings);
            println!("Tried {label}={mid}: {new_outcome}");
            if new_outcome.kind != OutcomeKind::Works {
                *outcome = new_outcome;
                min_broken = mid;
                broken = mid;
            } else {
                works = mid;
            }
        }
        set(settings, min_broken);
        min_broken
    }

    fn shrink_from_front(&mut self, settings: &CompileSettings, executed_ksplang: u64) -> Option<ReproOutcome> {
        let candidates = self.collect_candidate_positions(executed_ksplang);

        println!("front-shrinking: {} candidates...", candidates.len());

        for &(candidate_ip, trace_index) in candidates.iter().rev() {
            if candidate_ip == self.start_state.ip {
                continue;
            }

            let mut forward_state = self.start_state.clone();
            let mut forward_options = self.options.clone();
            forward_options.stop_after = self.start_state.instructions_run + trace_index as u64;
            
            if run_state(&mut forward_state, &forward_options).is_err() || forward_state.ip != candidate_ip {
                println!("Failed to execute to position {} (trace index {})", candidate_ip, trace_index);
                continue;
            }

            let old_start_state = mem::replace(&mut self.start_state, forward_state);
            let new_outcome = self.compile_and_reproduce(settings);

            println!("front-shrinking: tried position {}: {}", candidate_ip, new_outcome);

            match new_outcome.kind {
                OutcomeKind::Works => {
                    self.start_state = old_start_state;
                }
                _ => {
                    println!("front-shrinking: success {} -> {}", executed_ksplang, new_outcome.executed_ksplang);
                    return Some(new_outcome);
                }
            }
        }
        println!("front-shrinking: all {} candidates don't reproduce", candidates.len());
        None
    }

    fn collect_candidate_positions(&self, expected_runtime: u64) -> Vec<(usize, usize)> {
        let mut candidates = Vec::new();
        let trace = self.collect_trace(expected_runtime as usize);
        println!("Collected trace with {} ops, expected {}", trace.ips.len(), expected_runtime);

        for i in 0..trace.ips.len().saturating_sub(1) {
            if let (Some(&op), Some(&next_op)) = (self.start_state.ops.get(trace.ips[i]), self.start_state.ops.get(trace.ips[i + 1])) {
                if op == crate::ops::Op::DigitSum && next_op == crate::ops::Op::DigitSum {
                    candidates.push((trace.ips[i], i));
                }
            }
        }

        candidates
    }

    fn compile_and_reproduce(&self, settings: &CompileSettings) -> ReproOutcome {
        let block = match panic::catch_unwind(|| self.build_block(settings)) {
            Ok(block) => block,
            Err(err) => return ReproOutcome { executed_ksplang: 0, kind: OutcomeKind::Error(format_panic_message("Compilation", err)) }
        };

        match panic::catch_unwind(|| {
            let mut stack = self.start_state.stack.clone();
            let mut regfile = RegFile::new_debug();
            let r = OptimizingVM::interpret_block(&block, &mut stack, &mut regfile, self.vm.conf.error_as_deopt)?;
            Ok((r, stack))
        }) {
            Ok(Ok((result, optimized_stack))) => {
                let optimized_ip = result.next_ip;
                if let Some((reference_stack, reference_ip)) = self.run_reference(result.executed_ksplang) {
                    if optimized_stack != reference_stack || optimized_ip != reference_ip {
                        return ReproOutcome {
                            executed_ksplang: result.executed_ksplang,
                            kind: OutcomeKind::Mismatch {
                                optimized_stack,
                                optimized_ip,
                                reference_stack,
                                reference_ip,
                            },
                        };
                    }
                    ReproOutcome { executed_ksplang: result.executed_ksplang, kind: OutcomeKind::Works }
                } else {
                    ReproOutcome {
                        executed_ksplang: result.executed_ksplang,
                        kind: OutcomeKind::Error("reference execution failed".to_string()),
                    }
                }
            }
            Ok(Err(err)) => ReproOutcome {
                executed_ksplang: 0,
                kind: OutcomeKind::OpError(err),
            },
            Err(err) => ReproOutcome { executed_ksplang: 0, kind: OutcomeKind::Error(format_panic_message("Interpreter", err)) },
        }
    }

    fn build_block(&self, settings: &CompileSettings) -> OptimizedBlock {
        if settings.use_trace {
            let trace = self.collect_trace(settings.interpret_limit);
            self.compile_with_tracer(trace, settings)
        } else {
            self.compile_with_tracer(NoTrace(), settings)
        }
    }

    fn compile_with_tracer<T>(&self, tracer: T, settings: &CompileSettings) -> OptimizedBlock
    where
        T: TraceProvider,
    {
        let mut pre = Precompiler::new(
            &self.start_state.ops,
            self.start_state.stack.len(),
            self.start_state.reversed,
            self.start_state.ip,
            settings.interpret_limit,
            settings.soft_limits,
            None,
            GraphBuilder::new(self.start_state.ip),
            tracer,
        );
        if let Some(v) = settings.override_verbosity {
            pre.conf.verbosity = v;
            pre.g.conf = Box::leak(Box::new(pre.conf.clone()));
        }
        pre.bb_limit = settings.bb_limit;
        pre.instr_limit = settings.instr_limit;
        pre.interpret();
        let osmibytecode = (settings.use_osmibyte && self.vm.conf.allow_osmibyte_backend)
            .then(|| OsmibytecodeBlock::from_cfg(&pre.g));
        self.vm.build_block(self.start_state.ip, self.start_state.reversed, pre.g, osmibytecode)
    }

    fn collect_trace(&self, interpret_limit: usize) -> ActualTracer {
        let (backup, mut traced_state) = self.start_state.clone().swap_tracer(ActualTracer::default());
        traced_state.tracer.start_block_location = traced_state.ip;
        traced_state.tracer.reversed = traced_state.reversed;
        let interpret_hint = (interpret_limit as u32).saturating_mul(2).max(1);
        traced_state.tracer.max_count = cmp::max(self.vm.conf.trace_limit, interpret_hint);
        let mut options = self.options.clone();
        options.stop_after = traced_state.instructions_run + interpret_limit as u64;
        let _run_result = run_state(&mut traced_state, &options);
        let (trace, _) = traced_state.swap_tracer(backup);
        trace
    }

    fn run_reference(&self, executed: u64) -> Option<(Vec<i64>, usize)> {
        let mut reference_state = self.start_state.clone().swap_tracer(NoStats::default()).1;
        let mut options = self.options.clone();
        options.stop_after = self.start_state.instructions_run + executed;
        run_state(&mut reference_state, &options).ok()?;
        Some((reference_state.stack, reference_state.ip))
    }

    fn panic_with_summary(
        &self,
        settings: &CompileSettings,
        outcome: &ReproOutcome,
        initial_mismatch: Option<(&[i64], usize)>,
        initial_baseline: Option<(&[i64], usize)>,
    ) -> ! {
        println!("\nRecompiling with verbosity {}...", self.vm.conf.shrinker_final_verbosity);
        let mut changed_settings = settings.clone();
        changed_settings.override_verbosity = Some(self.vm.conf.shrinker_final_verbosity);
        let block = self.build_block(&changed_settings);

        println!("\nCFG:\n{}", block.cfg.unwrap());
        if let Some(obc) = &block.osmibytecode {
            println!("\nOsmibytecode: {}", obc);
        }

        if changed_settings.interpret_limit > 1 {
            changed_settings.override_verbosity = Some(0);
            changed_settings.interpret_limit -= 1;
            println!("Recompiling with limit-1 = {}...", changed_settings.interpret_limit);
            debug_assert_eq!(self.compile_and_reproduce(&changed_settings).kind, OutcomeKind::Works);
            let ok_block = self.build_block(&changed_settings);

            println!("\nOK CFG for comparison\n{}", ok_block.cfg.unwrap());
            if let Some(obc) = &ok_block.osmibytecode {
                println!("\nOK Osmibytecode: {}", obc);
            }
        }

        println!("shrinker report:");
        println!(
            "  origin ip {} reversed={} stack_len={}",
            self.start_state.ip,
            self.start_state.reversed,
            self.start_state.stack.len()
        );
        println!(
            "  recompiled with trace={} use_osmibyte={} limits={{bb: {}, instr: {}, interpret: {}}}",
            settings.use_trace,
            settings.use_osmibyte,
            settings.bb_limit,
            settings.instr_limit,
            settings.interpret_limit
        );
        println!("  outcome: {outcome}");
        if let Some((stack, ip)) = initial_mismatch {
            println!(
                "  initial optimized next_ip {} stack {}",
                ip,
                format_stack_preview(stack)
            );
        } else {
            println!("  initial optimized result: panic");
        }
        if let Some((stack, ip)) = initial_baseline {
            println!(
                "  initial reference next_ip {} stack {}",
                ip,
                format_stack_preview(stack)
            );
        }

        panic!("shrinker: mismatch reproduced at {}: {outcome:?}", self.start_state.ip);
    }
}

fn format_stack_preview(stack: &[i64]) -> String {
    let len = stack.len();
    if len <= STACK_PREVIEW {
        return format!("{:?}", stack);
    }
    let head: Vec<_> = stack.iter().take(4).copied().collect();
    let tail: Vec<_> = stack.iter().rev().take(STACK_PREVIEW - 4).copied().collect();
    format!(
        "{:?} ... {:?} (len {})",
        head,
        tail.into_iter().rev().collect::<Vec<_>>(),
        len
    )
}

fn format_panic_message(label: &str, err: Box<dyn std::any::Any + Send>) -> String {
    if let Some(errmsg) = err.downcast_ref::<String>() {
        format!("{label} panicked: {errmsg}")
    } else if let Some(errmsg) = err.downcast_ref::<&str>() {
        format!("{label} panicked: {errmsg}")
    } else {
        format!("{label} panicked: {err:?} ({:?})", err.type_id())
    }
}
