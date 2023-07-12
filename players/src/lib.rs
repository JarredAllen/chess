//! Traits for an arbitrary player

use core::ops::{Deref, DerefMut};

use board::LongAlgebraicNotationMove;

/// A player in a game
///
/// This trait is generic over how the players decides what to do, so GUI and AI players can both
/// implement this.
pub trait Player {
    /// Overwrite the current state with the given position and sequence of moves
    fn position(&mut self, fen: &str, moves: &[LongAlgebraicNotationMove]);

    /// Decide on a move to make
    ///
    /// This function should both return the move and update `self` to reflect the move being made.
    fn make_move(&mut self) -> LongAlgebraicNotationMove;

    /// React to the opponent making the given move
    fn react_to_move(&mut self, opponent_move: LongAlgebraicNotationMove);
}

impl<Ref: DerefMut> Player for Ref
where
    <Ref as Deref>::Target: Player,
{
    fn position(&mut self, fen: &str, moves: &[LongAlgebraicNotationMove]) {
        self.deref_mut().position(fen, moves);
    }

    fn make_move(&mut self) -> LongAlgebraicNotationMove {
        self.deref_mut().make_move()
    }

    fn react_to_move(&mut self, opponent_move: LongAlgebraicNotationMove) {
        self.deref_mut().react_to_move(opponent_move);
    }
}
