use clap::Parser;
use ksplang::ops::Op;
use ksplang::parser;
use ksplang::vm::VMOptions;
use std::io::{BufRead, Read};
use std::time::Duration;

/// Run a ksplang program.
#[derive(Parser, Debug)]
#[command()]
struct Args {
    /// File containing a ksplang program.
    #[arg()]
    ksplang_file: String,
    /// Maximum stack size.
    #[arg(long, short = 'm', default_value_t = 2097152)]
    max_stack_size: usize,
    /// A limit for the number of executed instructions.
    /// If the limit is reached, the program will be stopped with an error.
    #[arg(long, short = 'l')]
    op_limit: Option<u64>,
    /// Print statistics after running the program.
    #[arg(long, short = 's')]
    stats: bool,
    /// A shorthand for setting both `--text-input` and `--text-output`.
    #[arg(long, short = 't')]
    text: bool,
    /// Print the stack as text (interpret numbers as Unicode code points).
    #[arg(long)]
    text_output: bool,
    /// Read the stack as text (interpret Unicode code points as numbers).
    #[arg(long)]
    text_input: bool,
    /// Optional file containing pi digits; required only when using the kPi
    /// instruction with more than 10 million digits.
    ///
    /// The file should contain ASCII digits 0-9 (other characters are ignored) and should start with 3.
    #[arg(long)]
    pi_digit_file: Option<String>,
    /// Allow optimizing tracing JIT
    #[arg(long, short='o')]
    optimize: bool,
}

#[derive(Debug, Clone, Copy)]
enum StackEncoding {
    Numbers,
    Text,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let input_encoding =
        if args.text || args.text_input { StackEncoding::Text } else { StackEncoding::Numbers };
    let output_encoding =
        if args.text || args.text_output { StackEncoding::Text } else { StackEncoding::Numbers };

    let ops: Vec<Op> = read_program_from_file(&args.ksplang_file)?;
    let stack: Vec<i64> = read_stack_from_stdin(input_encoding)?;

    let pi_digits = match args.pi_digit_file {
        Some(file) => get_pi_digits_from_file(&file)?,
        None => get_builtin_pi_digits(),
    };
    let options = VMOptions::new(
        &stack,
        args.max_stack_size,
        &pi_digits,
        args.op_limit.unwrap_or(u64::MAX),
        u64::MAX,
    );

    let start_time = std::time::Instant::now();
    let result = if args.optimize {
        let mut vm = ksplang::vm::OptimizingVM::new(ops, true);
        vm.run(stack.clone(), options)?
    } else {
        ksplang::vm::run(&ops, options)?
    };
    let elapsed = start_time.elapsed();

    if args.stats {
        print_stats(result.instruction_counter, elapsed);
    }

    print_output(&result.stack, output_encoding);

    Ok(())
}

fn read_program_from_file(file: &str) -> Result<Vec<Op>, anyhow::Error> {
    let file = std::fs::File::open(file)?;
    let reader = std::io::BufReader::new(file);
    let mut ops: Vec<Op> = Vec::new();
    for line in reader.lines() {
        let line = line?;
        for word in line.split_whitespace() {
            ops.push(parser::parse_word(&word)?);
        }
    }
    Ok(ops)
}

fn read_stack_from_stdin(encoding: StackEncoding) -> Result<Vec<i64>, anyhow::Error> {
    let mut stack: Vec<i64> = Vec::new();
    match encoding {
        StackEncoding::Numbers => {
            for line in std::io::stdin().lock().lines() {
                let line = line?;
                for word in line.split_whitespace() {
                    stack.push(word.parse()?);
                }
            }
        }
        StackEncoding::Text => {
            let mut string = String::new();
            std::io::stdin().lock().read_to_string(&mut string)?;
            for c in string.chars() {
                stack.push(c as i64);
            }
        }
    }
    Ok(stack)
}

fn print_output(stack: &[i64], encoding: StackEncoding) {
    match encoding {
        StackEncoding::Numbers => {
            for &value in stack {
                println!("{}", value);
            }
        }
        StackEncoding::Text => {
            for &value in stack {
                print!("{}", std::char::from_u32(value as u32).unwrap_or(char::REPLACEMENT_CHARACTER));
            }
        }
    }
}

fn print_stats(instruction_counter: u64, elapsed: Duration) {
    let instructions_per_second = instruction_counter as f64 / elapsed.as_secs_f64();
    eprintln!("Execution time: {:?}", elapsed);
    eprintln!(
        "Instructions executed: {} ({}/s)",
        instruction_counter,
        match instructions_per_second {
            n if n >= 1_000_000.0 => format!("{:.1}M", n / 1_000_000.0),
            n if n >= 1_000.0 => format!("{:.1}k", n / 1_000.0),
            n => format!("{:.1}", n),
        }
    );
}

fn get_builtin_pi_digits() -> Vec<i8> {
    include_str!("../../pi-10million.txt")
        .bytes()
        .map(|b| b as char)
        .filter(|&x| x.is_digit(10))
        .map(|x| x.to_digit(10).unwrap() as i8)
        .collect()
}

fn get_pi_digits_from_file(file: &str) -> Result<Vec<i8>, anyhow::Error> {
    let file = std::fs::File::open(file)?;
    let reader = std::io::BufReader::new(file);
    let mut digits: Vec<i8> = Vec::new();
    for line in reader.lines() {
        let line = line?;
        for c in line.chars() {
            if c.is_digit(10) {
                digits.push(c.to_digit(10).unwrap() as i8);
            }
        }
    }
    Ok(digits)
}
