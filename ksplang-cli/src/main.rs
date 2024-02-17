use clap::Parser;
use ksplang::ops::Op;
use ksplang::parser;
use ksplang::vm::VMOptions;
use std::io::BufRead;

fn get_pi_digits() -> Vec<i8> {
    include_str!("../../pi-10million.txt")
        .chars()
        .filter(|&x| x.is_digit(10))
        .map(|x| x.to_digit(10).unwrap() as i8)
        .collect()
}

/// Run a ksplang program.
#[derive(Parser, Debug)]
#[command()]
struct Args {
    /// File containing a ksplang program.
    #[arg()]
    file: String,
    /// Maximum stack size.
    #[arg(long, short = 's', default_value_t = 2097152)]
    max_stack_size: usize,
    /// A limit for the number of executed operations.
    /// If the limit is reached, the program will be stopped with an error.
    #[arg(long, short = 'l')]
    op_limit: Option<u64>,
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

fn read_stack_from_stdin() -> Result<Vec<i64>, anyhow::Error> {
    let mut stack: Vec<i64> = Vec::new();
    for line in std::io::stdin().lock().lines() {
        let line = line?;
        for word in line.split_whitespace() {
            stack.push(word.parse()?);
        }
    }
    Ok(stack)
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let ops: Vec<Op> = read_program_from_file(&args.file)?;
    let stack: Vec<i64> = read_stack_from_stdin()?;

    let pi_digits = get_pi_digits();
    let options = VMOptions::new(
        &stack,
        args.max_stack_size,
        &pi_digits,
        args.op_limit.unwrap_or(u64::MAX),
        u64::MAX,
    );
    let result = ksplang::vm::run(&ops, options)?;
    for &value in result.stack.iter() {
        println!("{}", value);
    }

    Ok(())
}
