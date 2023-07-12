//! A player which makes purely random moves

use bitboard::BitboardRepresentation;
use board::{Board, LongAlgebraicNotationMove};

use rand::{rngs::SmallRng, seq::IteratorRandom, SeedableRng};

/// A player which makes purely random moves
///
/// The name is pronounced like "Monkey"
#[derive(Debug)]
pub struct MonkePlayer {
    /// The state of the board
    board: BitboardRepresentation,
    /// How we decide what to do
    rng: SmallRng,
}

impl MonkePlayer {
    /// Create a new player with the initial board state.
    pub fn new() -> Self {
        Self {
            board: BitboardRepresentation::INITIAL_STATE,
            rng: SmallRng::from_entropy(),
        }
    }
}

impl players::Player for MonkePlayer {
    fn position(&mut self, fen: &str, moves: &[LongAlgebraicNotationMove]) {
        let mut board = BitboardRepresentation::from_fen(fen);
        for mv in moves {
            board.make_long_move(*mv).expect("Failed to make move");
        }
        self.board = board;
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

impl Default for MonkePlayer {
    fn default() -> Self {
        Self::new()
    }
}
