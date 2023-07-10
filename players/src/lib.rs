//! Traits for an arbitrary player

use board::LongAlgebraicNotationMove;

/// A player in a game
///
/// This trait is generic over how the players decides what to do, so GUI and AI players can both
/// implement this.
pub trait Player {
    /// Construct a new player from the given position
    fn position(fen: &str, moves: &[LongAlgebraicNotationMove]) -> Self;

    /// Decide on a move to make
    ///
    /// This function should both return the move and update `self` to reflect the move being made.
    fn make_move(&mut self) -> LongAlgebraicNotationMove;

    /// React to the opponent making the given move
    fn react_to_move(&mut self, opponent_move: LongAlgebraicNotationMove);
}
