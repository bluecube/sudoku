use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn escragot_benchmark(c: &mut Criterion) {
    let board = sudoku::Board::example_boards()["escragot"].clone();

    c.bench_function("escragot", |b| b.iter(|| board.solve()));
}

criterion_group!(benches, escragot_benchmark);
criterion_main!(benches);
