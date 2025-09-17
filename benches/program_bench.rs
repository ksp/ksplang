use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;

use ksplang::{ops::Op, parser::parse_program, vm::VMOptions};

fn parse_in_num(str: &str) -> Vec<i64> {
    let mut stack = vec![];
    for line in str.lines() {
        for word in line.split_whitespace() {
            stack.push(word.parse().unwrap());
        }
    }
    stack
}

fn parse_in_txt(str: &str) -> Vec<i64> {
    let mut stack = vec![];
    for c in str.chars() {
        stack.push(c as i64);
    }
    stack
}

fn run(ops: &[Op], input: &[i64]) {
    let options = VMOptions::new(input, 2097152, &[], 10_000_000_000, u64::MAX);
    black_box(ksplang::vm::run(&ops, options).unwrap());
}

fn criterion_benchmark(c: &mut Criterion) {
    // programs are taken from: https://github.com/Sejsel/aoc2024-ksplang

    // target at most 100ms
    let fast_tests: Vec<(String, Vec<Op>, Vec<i64>)> = vec![
        (format!("aoc24-1-1"), parse_program(include_str!("programs/aoc24-1-1.ksplang")).unwrap(), parse_in_num(include_str!("programs/aoc24-1-short.in"))),
        (format!("aoc24-1-2"), parse_program(include_str!("programs/aoc24-1-2.ksplang")).unwrap(), parse_in_num(include_str!("programs/aoc24-1-short.in"))),
        (format!("aoc24-2-1"), parse_program(include_str!("programs/aoc24-2-1.ksplang")).unwrap(), parse_in_txt(include_str!("programs/aoc24-2-short.in"))),
        (format!("aoc24-3-2"), parse_program(include_str!("programs/aoc24-3-2.ksplang")).unwrap(), parse_in_txt(include_str!("programs/aoc24-3-short.in"))),
        (format!("aoc24-7-1"), parse_program(include_str!("programs/aoc24-7-1.ksplang")).unwrap(), parse_in_txt(include_str!("programs/aoc24-7-short.in"))),
    ];
    // target at most few seconds
    let slow_tests: Vec<(String, Vec<Op>, Vec<i64>)> = vec![
        (format!("aoc24-1-1"), parse_program(include_str!("programs/aoc24-1-1.ksplang")).unwrap(), parse_in_num(include_str!("programs/aoc24-1.in"))),
        (format!("aoc24-1-2"), parse_program(include_str!("programs/aoc24-1-2.ksplang")).unwrap(), parse_in_num(include_str!("programs/aoc24-1.in"))),
        (format!("aoc24-2-1"), parse_program(include_str!("programs/aoc24-2-1.ksplang")).unwrap(), parse_in_txt(include_str!("programs/aoc24-2.in"))),
        (format!("aoc24-3-2"), parse_program(include_str!("programs/aoc24-3-2.ksplang")).unwrap(), parse_in_txt(include_str!("programs/aoc24-3.in"))),
        (format!("aoc24-7-1"), parse_program(include_str!("programs/aoc24-7-1.ksplang")).unwrap(), parse_in_txt(include_str!("programs/aoc24-7.in"))),
    ];

    let mut group = c.benchmark_group("full_program");

    for (name, prog, input) in fast_tests.iter() {
        group.bench_function(BenchmarkId::from_parameter(format!("{name}")), |bencher: &mut criterion::Bencher<'_>| {
            bencher.iter(|| run(black_box(&prog), black_box(&input)));
        });
    }
    group.finish();

    let mut slow_group = c.benchmark_group("full_program_slow");
    slow_group.sample_size(10);
    slow_group.sampling_mode(criterion::SamplingMode::Flat);
    for (name, prog, input) in slow_tests.iter() {
        slow_group.bench_function(BenchmarkId::from_parameter(format!("{name}")), |bencher: &mut criterion::Bencher<'_>| {
            bencher.iter(|| run(black_box(&prog), black_box(&input)));
        });
    }
    slow_group.finish();
}

criterion_group!(name = benches; config = Criterion::default(); targets = criterion_benchmark);
criterion_main!(benches);
