use std::env;

fn main() {
    for arg in env::args().skip(1) {
        let board = sudoku::Board::from_flat_str(&arg).unwrap();
        sudoku::solve_and_print(board);
    }
}
