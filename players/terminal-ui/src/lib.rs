//! A player which makes purely random moves

use std::io::{self, Write};

use bitboard::BitboardRepresentation;
use board::{AlgebraicNotationMove, Board, LongAlgebraicNotationMove};

/// An input for a human typing in the terminal
pub struct TerminalUIPlayer {
    board: BitboardRepresentation,
}

impl players::Player for TerminalUIPlayer {
    fn position(fen: &str, moves: &[LongAlgebraicNotationMove]) -> Self {
        let mut board = BitboardRepresentation::from_fen(fen);
        for mv in moves {
            board.make_long_move(*mv).expect("Failed to make move");
        }
        Self { board }
    }

    fn react_to_move(&mut self, opponent_move: LongAlgebraicNotationMove) {
        let mv = self
            .board
            .detail_long_algebraic_move(opponent_move)
            .expect("Failed to make opponent move");
        self.board
            .do_move_if_legal(mv)
            .expect("Failed to make move");
        println!("Opponent made move: {opponent_move}");
    }

    fn make_move(&mut self) -> LongAlgebraicNotationMove {
        let algebraic = {
            print!("Please input your move in algebraic notation: ");
            let _ = io::stdout().flush();
            let mut buffer = String::new();
            io::stdin()
                .read_line(&mut buffer)
                .expect("Error reading human input");
            buffer
                .trim()
                .parse::<AlgebraicNotationMove>()
                .expect("Error parsing algebraic notation")
        };
        let mv = self
            .board
            .detail_algebraic_move(algebraic)
            .expect("Illegal move provided");
        self.board
            .do_move_if_legal(mv)
            .expect("Illegal move provided");
        mv.into()
    }
}
