use criterion::{criterion_group, criterion_main, Criterion};

fn solve_benchmark(c: &mut Criterion) {
    for (name, board) in sudoku::Board::example_boards() {
        c.bench_function(name, |b| b.iter(|| board.solve(5)));
    }
}

criterion_group!(benches, solve_benchmark);
criterion_main!(benches);
