use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;

use ksplang::funkcia::{funkcia};

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
    ];
    for &(a, b) in pairs.iter() {
        group.bench_with_input(BenchmarkId::from_parameter(format!("{a}-{b}")), &(a, b), |bencher, &(a, b)| {
            bencher.iter(|| black_box(funkcia(black_box(a), black_box(b))));
        });
    }
    group.finish();
}

criterion_group!(name = benches; config = Criterion::default(); targets = criterion_benchmark);
criterion_main!(benches);
