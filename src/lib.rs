use std::collections::BTreeMap;
use std::fmt::Display;
use std::num::NonZeroU8;
use std::ops::{BitAnd, Index, IndexMut};

use anyhow::bail;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Board {
    fields: [[Option<NonZeroU8>; 9]; 9],
}

impl Board {
    pub fn from_flat_str(s: &str) -> anyhow::Result<Self> {
        let mut chars = s.chars();
        let mut fields = [[None; 9]; 9];
        for y in 0..9 {
            for x in 0..9 {
                let c = chars.next().ok_or_else(|| {
                    anyhow::anyhow!("Flat string has too few characters (needs exactly 81)")
                })?;

                if let Some(v) = c.to_digit(10).filter(|v| *v != 0) {
                    fields[y][x] = Some((v as u8).try_into().unwrap());
                } else if c != ' ' && c != '.' {
                    anyhow::bail!(
                        "Wrong character at {}. Allowed characters are '1'-'9' and '.' or ' '.",
                        9 * y + x
                    );
                }
            }
        }
        if chars.next().is_some() {
            anyhow::bail!("Flat string has too many characters (needs exactly 81)");
        }

        Ok(Board { fields })
    }

    pub fn to_flat_str(&self) -> String {
        self.fields
            .iter()
            .flat_map(|row| row.map(Self::format_cell))
            .collect::<String>()
    }

    pub fn matches(&self, pattern: &Board) -> bool {
        let self_fields = self.fields.iter().flat_map(|row| row.iter());
        let pattern_fields = pattern.fields.iter().flat_map(|row| row.iter());

        let mismatch = self_fields
            .zip(pattern_fields)
            .any(|(value, pattern)| pattern.is_some_and(|pattern| *value != Some(pattern)));

        !mismatch
    }

    pub fn is_valid(&self) -> bool {
        self.to_bit_sets().is_ok()
    }

    pub fn is_solved(&self) -> bool {
        self.fields
            .iter()
            .flat_map(|row| row.iter())
            .all(Option::is_some)
    }

    pub fn solve(&self, max_results: usize) -> anyhow::Result<Vec<Board>> {
        let mut stack = vec![SolutionInProgress::new(self.clone())?];
        let mut result = Vec::new();

        while let Some(mut sol) = stack.pop() {
            if !sol.solve_simple() {
                // No solution -- just stop this branch completely
                continue;
            }
            if let Some((x, y)) = sol.empty_fields.pop() {
                let mut available = sol.bit_sets.get_available(x, y);
                while let Some(v) = available.pop() {
                    let mut cloned_sol = sol.clone();
                    cloned_sol.set_value(x, y, v);
                    stack.push(cloned_sol);
                }
            } else {
                // There are no more empty fields, the board is solved
                result.push(sol.into_board());
                if result.len() >= max_results {
                    break;
                }
            }
        }

        Ok(result)
    }

    fn to_bit_sets(&self) -> anyhow::Result<(BoardBitSets, PositionSet)> {
        let mut bit_sets = BoardBitSets::new();
        let mut empty_fields = PositionSet::new_empty();

        for y in 0..9 {
            for x in 0..9 {
                if let Some(v) = self[(x, y)] {
                    bit_sets.try_set_value(x, y, v)?;
                } else {
                    empty_fields.add(x, y);
                };
            }
        }

        Ok((bit_sets, empty_fields))
    }

    /// Formats a single value to character.
    /// Result is either '.', or a digit 1-9.
    /// Panics for out of range values.
    fn format_cell(v: Option<NonZeroU8>) -> char {
        v.map_or('.', |v| char::from_digit(v.get() as u32, 10).unwrap())
    }

    pub fn example_boards() -> BTreeMap<&'static str, Board> {
        let data = [
            "easy",
            "3.5629..77.61.8   8 1   265  3  5 7 687      2  7  6  47958  2 1  43 5 9  89    6",
            "hard",
            "96.....1.......8723......9.5.4..6........1..8...9..4...7..8.1...2.........927....",
            "multiple solutions",
            "174832596593461278..2957..1..75..9...197.36.5435.968.73.16..7599.8.75.6.7563.9.82",
            "unsolvable",
            "..2.6.3...5.8...4.1....7.69.7.....5...9.....23.....6...6..5.1....42.....8....3...",
            "escragot",
            "1....7.9..3..2...8..96..5....53..9...1..8...26....4...3......1..41.....7..7...3..",
            "hard1",
            ".....6....59.....82....8....45........3........6..3.54...325..6..................",
        ];

        data.chunks_exact(2)
            .map(|subslice| (subslice[0], Board::from_flat_str(subslice[1]).unwrap()))
            .collect()
    }
}

impl Index<(usize, usize)> for Board {
    type Output = Option<NonZeroU8>;

    fn index(&self, index: (usize, usize)) -> &Self::Output {
        let (x, y) = index;
        assert!(
            x < 9 && y < 9,
            "Both X and Y coordinates must be smaller than 9"
        );
        return &self.fields[y][x];
    }
}

impl IndexMut<(usize, usize)> for Board {
    fn index_mut(&mut self, index: (usize, usize)) -> &mut Self::Output {
        let (x, y) = index;
        assert!(
            x < 9 && y < 9,
            "Both X and Y coordinates must be smaller than 9"
        );
        return &mut self.fields[y][x];
    }
}

impl Display for Board {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for y in 0..9 {
            for x in 0..9 {
                write!(f, "{}", Self::format_cell(self[(x, y)]))?;
                if x == 2 || x == 5 {
                    write!(f, "|")?;
                }
            }
            writeln!(f, "")?;
            if y == 2 || y == 5 {
                writeln!(f, "---+---+---")?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct BoardBitSets {
    row: [ValueSet; 9],
    col: [ValueSet; 9],
    block: [ValueSet; 9],
}

impl BoardBitSets {
    fn new() -> Self {
        BoardBitSets {
            row: [ValueSet::new(); 9],
            col: [ValueSet::new(); 9],
            block: [ValueSet::new(); 9],
        }
    }

    /// Return set of values that are unavailable for given grid position
    fn get_available(&self, x: usize, y: usize) -> ValueSet {
        let block_index = Self::get_block_index(x, y);
        self.row[y] & self.col[x] & self.block[block_index]
    }

    fn try_set_value(&mut self, x: usize, y: usize, value: NonZeroU8) -> anyhow::Result<()> {
        let block_index = Self::get_block_index(x, y);

        if !self.row[y].contains(value) {
            bail!("Cannot place value {value} at {x}, {y} -- row conflict")
        } else {
            self.row[y].remove(value);
        }

        if !self.col[x].contains(value) {
            bail!("Cannot place value {value} at {x}, {y} -- column conflict")
        } else {
            self.col[x].remove(value);
        }

        if !self.block[block_index].contains(value) {
            bail!("Cannot place value {value} at {x}, {y} -- column conflict")
        } else {
            self.block[block_index].remove(value);
        }

        Ok(())
    }

    fn set_value(&mut self, x: usize, y: usize, value: NonZeroU8) {
        let block_index = Self::get_block_index(x, y);

        self.row[y].remove(value);
        self.col[x].remove(value);
        self.block[block_index].remove(value);
    }

    fn get_block_index(x: usize, y: usize) -> usize {
        let block_x = x / 3;
        let block_y = y / 3;

        block_x + 3 * block_y
    }

    fn print(&self) {
        println!("Row options: ");
        self.row.iter().for_each(|bitset| {
            bitset.print();
            println!("")
        });
        println!("Col options: ");
        self.col.iter().for_each(|bitset| {
            bitset.print();
            println!("")
        });
        println!("Block options: ");
        self.block.iter().for_each(|bitset| {
            bitset.print();
            println!("")
        });
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct ValueSet {
    bits: u16,
}

impl ValueSet {
    fn new() -> Self {
        Self {
            bits: (1u16 << 9) - 1,
        }
    }

    fn is_empty(&self) -> bool {
        self.bits == 0
    }

    fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }

    fn pop(&mut self) -> Option<NonZeroU8> {
        if self.is_empty() {
            None
        } else {
            let tz = self.bits.trailing_zeros();
            self.bits &= !(1 << tz);
            Some((tz as u8 + 1).try_into().unwrap())
        }
    }

    fn peek(&self) -> Option<NonZeroU8> {
        if self.is_empty() {
            None
        } else {
            let tz = self.bits.trailing_zeros();
            Some((tz as u8 + 1).try_into().unwrap())
        }
    }

    fn print(&self) {
        let mut cloned = self.clone();
        while let Some(v) = cloned.pop() {
            print!(" {v},");
        }
        println!();
    }

    fn remove(&mut self, value: NonZeroU8) {
        let index = value.get() - 1;
        self.bits &= !(1 << index);
    }

    fn contains(&self, value: NonZeroU8) -> bool {
        let index = value.get() - 1;
        self.bits & (1 << index) != 0
    }
}

impl BitAnd for ValueSet {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        ValueSet {
            bits: self.bits & rhs.bits,
        }
    }
}

#[derive(Clone, Debug)]
#[repr(transparent)]
struct PositionSet {
    bits: u128,
}

impl PositionSet {
    fn new_empty() -> Self {
        PositionSet { bits: 0 }
    }

    fn new(board: &Board) -> Self {
        let mut s = Self::new_empty();
        for y in 0..9 {
            for x in 0..9 {
                if board[(x, y)].is_none() {
                    s.add(x, y);
                }
            }
        }

        s
    }

    fn pop(&mut self) -> Option<(usize, usize)> {
        if self.bits == 0 {
            None
        } else {
            let index = self.bits.trailing_zeros() as usize;
            self.bits &= !(1u128 << index);

            Some((index % 9, index / 9))
        }
    }

    fn add(&mut self, x: usize, y: usize) {
        let index = x + 9 * y;
        self.bits |= 1 << index;
    }

    fn remove(&mut self, x: usize, y: usize) {
        let index = x + 9 * y;
        self.bits &= !(1 << index);
    }

    fn add_affected(&mut self, x: usize, y: usize, board: &Board) {
        for i in 0..9 {
            if board[(x, i)].is_none() {
                self.add(x, i);
            }
            if board[(i, y)].is_none() {
                self.add(i, y);
            }
        }

        let block_base_x = 3 * (x / 3);
        let block_base_y = 3 * (y / 3);
        for y in 0..3 {
            for x in 0..3 {
                let x = block_base_x + x;
                let y = block_base_y + y;
                if board[(x, y)].is_none() {
                    self.add(x, y);
                }
            }
        }
    }

    fn is_empty(&self) -> bool {
        self.bits == 0
    }

    fn print_positions(&self) {
        let mut cloned = self.clone();
        while let Some((x, y)) = cloned.pop() {
            print!("({x}, {y}), ");
        }
        println!("");
    }
}

#[derive(Clone, Debug)]
struct SolutionInProgress {
    board: Board,
    bit_sets: BoardBitSets,
    /// Set of all positions that might potentially have only one possible value
    to_check: PositionSet,
    empty_fields: PositionSet,
}

impl SolutionInProgress {
    pub fn new(board: Board) -> anyhow::Result<Self> {
        let (bit_sets, empty_fields) = board.to_bit_sets()?;
        let to_check = PositionSet::new(&board);
        Ok(SolutionInProgress {
            board,
            bit_sets,
            to_check,
            empty_fields,
        })
    }

    pub fn into_board(self) -> Board {
        self.board
    }

    /// Attempt to solve the sudoku in place using a very simple
    /// constraint based solver.
    /// Only dealing with single values.
    /// Returns false iff there is a contradiction in the board.
    pub fn solve_simple(&mut self) -> bool {
        while let Some((x, y)) = self.to_check.pop() {
            debug_assert!(self.board[(x, y)].is_none());

            let available = self.bit_sets.get_available(x, y);
            if available.is_empty() {
                return false;
            } else if available.len() == 1 {
                let v = available.peek().unwrap();

                self.set_value(x, y, v);
            }
        }

        true
    }

    fn set_value(&mut self, x: usize, y: usize, v: NonZeroU8) {
        assert!(self.board[(x, y)].is_none());
        self.board[(x, y)] = Some(v);
        self.bit_sets.set_value(x, y, v);
        self.to_check.add_affected(x, y, &self.board);
        self.empty_fields.remove(x, y);
    }
}

pub fn solve_and_print(board: Board) {
    println!("{}", board);
    assert!(board.is_valid());

    const MAX_SOLUTIONS: usize = 5;
    let solutions = board.solve(MAX_SOLUTIONS).unwrap();
    println!("Found {} solutions:", solutions.len());
    if solutions.len() == MAX_SOLUTIONS {
        println!("Number of solutions was limited, there are possibly more.");
    }
    for sol in solutions {
        println!("{}", sol);
        assert!(sol.is_valid());
        assert!(sol.matches(&board));
        assert!(sol.is_solved());
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use test_strategy::proptest;

    #[proptest]
    fn test_valid_flat_str_round_trip(#[strategy("[1-9.]{81}")] flat_str: String) {
        let board = Board::from_flat_str(&flat_str).unwrap();
        let roundtrip = board.to_flat_str();

        assert_eq!(roundtrip, flat_str)
    }

    #[test]
    fn example_sudokus() {
        for (name, board) in Board::example_boards() {
            println!("{name}");
            solve_and_print(board);
            println!();
        }
    }
}
