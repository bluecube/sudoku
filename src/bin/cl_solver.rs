use std::env;

fn main() {
    if env::args().len() == 1 {
        println!("Demo mode!");

        for (name, board) in sudoku::Board::example_boards() {
            println!();
            println!("{}", name);
            sudoku::solve_and_print(board);
        }
    }
    for arg in env::args().skip(1) {
        let board = sudoku::Board::from_flat_str(&arg).unwrap();
        sudoku::solve_and_print(board);
    }
}
