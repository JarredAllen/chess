//! A player which makes purely random moves

use std::io::{self, Write};

use bitboard::BitboardRepresentation;
use board::{AlgebraicNotationMove, Board, Color, LongAlgebraicNotationMove, Piece};

/// An input for a human typing in the terminal
pub struct TerminalUIPlayer {
    board: BitboardRepresentation,
}

impl TerminalUIPlayer {
    /// Create a new player with the initial board state
    pub const fn new() -> Self {
        Self {
            board: BitboardRepresentation::INITIAL_STATE,
        }
    }
}

impl players::Player for TerminalUIPlayer {
    fn position(&mut self, fen: &str, moves: &[LongAlgebraicNotationMove]) {
        let mut board = BitboardRepresentation::from_fen(fen);
        for mv in moves {
            board.make_long_move(*mv).expect("Failed to make move");
        }
        self.board = board;
    }

    fn react_to_move(&mut self, opponent_move: LongAlgebraicNotationMove) {
        let mv = self
            .board
            .detail_long_algebraic_move(opponent_move)
            .expect("Failed to make opponent move");
        let opponent_move = self.board.move_to_algebraic(mv);
        println!("Opponent made move: {opponent_move}");
        self.board
            .do_move_if_legal(mv)
            .expect("Failed to make move");
    }

    fn make_move(&mut self) -> LongAlgebraicNotationMove {
        display_board(&self.board, self.board.side_to_move);
        loop {
            let algebraic = loop {
                print!("Please input your move in algebraic notation: ");
                let _ = io::stdout().flush();
                let mut buffer = String::new();
                io::stdin()
                    .read_line(&mut buffer)
                    .expect("Error reading human input");
                match buffer.trim().parse::<AlgebraicNotationMove>() {
                    Ok(algebraic) => break algebraic,
                    Err(e) => {
                        println!("Error parsing algebraic notation of {}: {e}", buffer.trim())
                    }
                }
            };
            let mv = match self.board.detail_algebraic_move(algebraic) {
                Ok(mv) => mv,
                Err(e) => {
                    println!("Given move {algebraic} was illegal because: {e}");
                    continue;
                }
            };
            if let Err(e) = self.board.do_move_if_legal(mv) {
                println!("Given move {algebraic} was illegal because: {e}");
                continue;
            }
            break mv.into();
        }
    }
}

impl Default for TerminalUIPlayer {
    fn default() -> Self {
        Self::new()
    }
}

/// Display the given board to the terminal
///
/// This displays the board from the perspective of the given player.
fn display_board(board: &BitboardRepresentation, player: Color) {
    const BARRIER_LINE: &[u8] = "+---+---+---+---+---+---+---+---+\n".as_bytes();
    const SPACER_LINE: &[u8] = "|   |   |   |   |   |   |   |   |\n".as_bytes();
    let stdout = io::stdout();
    let mut stdout = stdout.lock();
    stdout.write_all(BARRIER_LINE).expect("Couldn't write");
    let ranks = match player {
        Color::White => [7, 6, 5, 4, 3, 2, 1, 0],
        Color::Black => [0, 1, 2, 3, 4, 5, 6, 7],
    };
    for rank in ranks {
        stdout.write_all(SPACER_LINE).expect("Couldn't write");
        for file in 0..8 {
            stdout.write_all("| ".as_bytes()).expect("Couldn't write");
            let square = board::BoardSquare::from_rank_file(rank, file);
            let piece = board.get(square);
            stdout
                .write_all(&[piece.map_or(' ', Piece::fen_letter) as u8])
                .expect("Couldn't write");
            stdout.write_all(" ".as_bytes()).expect("Couldn't write");
        }
        stdout.write_all("|\n".as_bytes()).expect("Couldn't write");
        stdout.write_all(SPACER_LINE).expect("Couldn't write");
        stdout.write_all(BARRIER_LINE).expect("Couldn't write");
    }
}
