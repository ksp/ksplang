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

const STACK_SEPARATOR: &str = "!";
const MAX_OPS: u64 = 1_000_000_000;
const MAX_STACK_SIZE: usize = 2_097_152;

fn main() -> anyhow::Result<()> {
    let pi_digits = get_pi_digits();
    let mut ops: Vec<Op> = Vec::new();
    let mut in_stack = false;
    let mut stack: Vec<i64> = Vec::new();
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("Failed to read a line from stdin.");
        for word in line.split_whitespace() {
            if !in_stack {
                if word == STACK_SEPARATOR {
                    in_stack = true;
                } else {
                    ops.push(parser::parse_word(&word)?);
                }
            } else {
                if word == STACK_SEPARATOR {
                    return Err(anyhow::anyhow!("Found two stack separators."));
                } else {
                    stack.push(word.parse()?);
                }
            }
        }
    }

    let options = VMOptions::new(&stack, MAX_STACK_SIZE, &pi_digits, MAX_OPS, u64::MAX);
    let result = ksplang::vm::run(&ops, options)?;
    for &value in result.stack.iter() {
        println!("{}", value);
    }

    Ok(())
}
