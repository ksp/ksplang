use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{Rng, SeedableRng};
use std::hint::black_box;

use ksplang::funkcia::funkcia;

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("funkcia");
    let pairs: &[(i64, i64)] = &[
        (2, 3),
        (3, 9),
        (10, 16),
        (24, 32),
        (1000, 1001),
        (1 << 61, (1 << 61) + 1),
        (3 << 62, 5 << 62),
        (7 << 61, i32::MAX as i64),
        (1_000_000_007, 1_000_000_009),
        (614_889_782_588_491_410, 307_444_891_294_245_705),
        (1_000_000_000_000_000_007, i64::MAX - 2),
        // (108, 225), // values taken from a real run of AOC24 3-2 solution
        // (114, 109),
        // (12426, 225),
        // (16300, 225),
        // (163, 100),
        // (3, 2),
        // (32, 109),
        // (33, 100),
        // (4, 3),
        // (49, 100),
        // (5, 3),
        // (5, 4),
        // (6225, 100),
        // (6640, 75),
        // (6641, 109),
        // (7, 113),
        // (7, 16),
        // (723870, 225),
        // (80, 75),
        // (80, 83),
        // (83, 75),
        // (996, 32),
    ];
    for &(a, b) in pairs.iter() {
        group.bench_with_input(BenchmarkId::from_parameter(format!("{a}-{b}")), &(a, b), |bencher, &(a, b)| {
            bencher.iter(|| black_box(funkcia(black_box(a), black_box(b))));
        });
    }
    let rng = rand::rngs::StdRng::from_seed([1; 32]);
    // generate i64 numbers 0..=i64::MAX
    let inputs: Vec<i64> = rng.random_iter().take(2048).collect();
    group.bench_function("random", |bencher| {
        bencher.iter(||
            for i in 0..inputs.len() {
                black_box(funkcia(black_box(inputs[i]), black_box(inputs[inputs.len() - 1 - i])));
            }
        );
    });
    group.finish();
}

criterion_group!(name = benches; config = Criterion::default(); targets = criterion_benchmark);
criterion_main!(benches);
