//! Variants of the game, and the different behaviors we need to implement them

use core::fmt;

use crate::{BoardSquare, Color, Piece};

mod traditional;

pub use traditional::{Traditional, TraditionalCastleOptions};

/// The details handled differently by supported chess variants
pub trait Variant: Copy + Eq + fmt::Debug {
    /// The stateful information needed to track castling
    type CastleState: Copy;

    /// The state at the start of a game
    ///
    /// This is used instead of implementing [`Default`] for `CastleState` so different variants
    /// can reuse the same type if desired.
    const INITIAL_CASTLE_STATE: Self::CastleState;

    /// Update the castle state according to the given move
    fn update_castle_state(
        state: Self::CastleState,
        move_piece: Piece,
        source_square: BoardSquare,
        target_square: BoardSquare,
    ) -> Self::CastleState;

    /// Display the castling state in FEN format
    fn castle_state_to_fen(state: Self::CastleState) -> String;

    /// Parse the state of castling from the term in FEN
    fn castle_state_from_fen(fen: &str) -> Self::CastleState;

    /// If the castle is allowed, update the state according to it being done
    fn is_castle_allowed(
        state: Self::CastleState,
        side: Color,
        kingside: bool,
    ) -> Option<Self::CastleState>;

    /// The FEN at which to start a game
    fn initial_fen<'a>() -> &'a str;
}
