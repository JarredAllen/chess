//! A player which makes purely random moves

use bitboard::BitboardRepresentation;
use board::{Board, LongAlgebraicNotationMove};

use rand::{rngs::SmallRng, seq::IteratorRandom, SeedableRng};

/// A player which makes purely random moves
///
/// The name is pronounced like "Monkey"
#[derive(Debug)]
pub struct MonkePlayer {
    board: BitboardRepresentation,
    rng: SmallRng,
}

impl players::Player for MonkePlayer {
    fn position(fen: &str, moves: &[LongAlgebraicNotationMove]) -> Self {
        let mut board = BitboardRepresentation::from_fen(fen);
        for mv in moves {
            board.make_long_move(*mv).expect("Failed to make move");
        }
        Self {
            board,
            rng: SmallRng::from_entropy(),
        }
    }

    fn react_to_move(&mut self, opponent_move: LongAlgebraicNotationMove) {
        self.board
            .make_long_move(opponent_move)
            .expect("Failed to make move");
    }

    fn make_move(&mut self) -> LongAlgebraicNotationMove {
        let mv = self.board.legal_moves().choose(&mut self.rng);
        if let Some(mv) = mv {
            // SAFETY: This move was produced to be legal
            unsafe { self.board.do_move(mv) };
            mv.into()
        } else {
            LongAlgebraicNotationMove::NULL_MOVE
        }
    }
}
