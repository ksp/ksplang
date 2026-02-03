use std::collections::BTreeSet;
use rustc_hash::FxHashMap as HashMap;

use crate::compiler::{
    cfg::GraphBuilder,
    config::get_config,
    ops::{BlockId, OptOp, ValueId},
    precompiler::{CallCacheContext, NoTrace, Precompiler},
};

#[derive(Debug, Clone)]
pub struct CachedCall {
    pub cfg: GraphBuilder,
    pub return_addr_param: ValueId,
    pub return_blocks: Vec<BlockId>,
}

#[derive(Debug)]
pub enum CallCacheResult {
    Hit(CachedCall),
    Miss,
    InProgress,
}

#[derive(Debug, Default)]
pub struct CallCache {
    cache: HashMap<usize, Option<CachedCall>>,
    in_progress: BTreeSet<usize>,
}

impl CallCache {
    pub fn new() -> Self {
        Self {
            cache: HashMap::default(),
            in_progress: BTreeSet::new(),
        }
    }

    pub fn get_or_create(
        &mut self,
        ops: &[crate::ops::Op],
        target_ip: usize,
        current_recursion_depth: u32,
    ) -> CallCacheResult {
        let conf = get_config();

        if current_recursion_depth >= conf.callcache_max_recursion {
            if conf.should_log(3) {
                println!("CallCache: recursion limit reached for IP {}", target_ip);
            }
            return CallCacheResult::Miss;
        }

        if self.in_progress.contains(&target_ip) {
            if conf.should_log(3) {
                println!("CallCache: recursion detected for IP {}", target_ip);
            }
            return CallCacheResult::InProgress;
        }

        if let Some(cached) = self.cache.get(&target_ip) {
            return match cached {
                Some(c) => CallCacheResult::Hit(c.clone()),
                None => CallCacheResult::Miss,
            };
        }

        if conf.should_log(2) {
            println!("CallCache: compiling function at IP {} (depth={})", target_ip, current_recursion_depth);
        }

        self.in_progress.insert(target_ip);
        let result = self.compile_function(ops, target_ip);
        self.in_progress.remove(&target_ip);

        match result {
            Some(cached) => {
                self.cache.insert(target_ip, Some(cached.clone()));
                CallCacheResult::Hit(cached)
            }
            None => {
                self.cache.insert(target_ip, None);
                CallCacheResult::Miss
            }
        }
    }

    fn compile_function(&mut self, ops: &[crate::ops::Op], target_ip: usize) -> Option<CachedCall> {
        let conf = get_config();

        let mut g = GraphBuilder::new(target_ip);

        // The return address is pushed by Call, so it's on top of the stack
        let return_addr = g.new_value();
        return_addr.range = 0..=(ops.len() as i64);
        let return_addr_id = return_addr.id;
        g.block_mut_(BlockId(0)).parameters.push(return_addr_id);
        // Push return addr on stack (will be at top)
        g.stack.push(return_addr_id);
        // Stack depth stays 0 - we haven't popped anything from caller's stack yet

        let mut precompiler = Precompiler::new(
            ops,
            100,  // initial stack has items from caller (below our return_addr)
            false,
            target_ip,
            conf.callcache_interpret_limit as usize,
            false,
            None,
            g,
            NoTrace(),
        );
        precompiler.bb_limit = conf.callcache_branch_limit as usize;
        precompiler.instr_limit = conf.callcache_instr_limit as usize;
        precompiler.callcache_ctx = Some(CallCacheContext {
            return_addr: Some(return_addr_id),
            return_blocks: Vec::new(),
        });

        precompiler.interpret();

        let g = precompiler.g;
        let return_blocks = precompiler.callcache_ctx.unwrap().return_blocks;

        // Reject if any non-return block ends with DeoptAssert(False)
        for block in g.reachable_blocks() {
            if return_blocks.contains(&block.id) { continue; }
            for instr in block.instructions.values() {
                if matches!(instr.op, OptOp::DeoptAssert(crate::compiler::osmibytecode::Condition::False)) {
                    if conf.should_log(3) {
                        println!("CallCache: rejecting IP {} due to Deopt(false) in block {}", target_ip, block.id);
                    }
                    return None;
                }
            }
        }

        if return_blocks.is_empty() {
            if conf.should_log(3) {
                println!("CallCache: rejecting IP {} - no return blocks", target_ip);
            }
            return None;
        }

        if conf.should_log(2) {
            println!("CallCache: cached IP {} with {} return blocks", target_ip, return_blocks.len());
            if conf.should_log(10) {
                println!("Cached CFG:\n{}", g);
            }
        }

        Some(CachedCall {
            cfg: g,
            return_addr_param: return_addr_id,
            return_blocks,
        })
    }
}
