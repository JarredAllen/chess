//! Variants of the game, and the different behaviors we need to implement them

use core::fmt;

use crate::{BoardSquare, Color, Piece, PieceKind};

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

bitflags::bitflags! {
    /// Which castles are allowed (the king and rook haven't moved yet)
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct TraditionalCastleOptions: u8 {
        const WhiteKingside = 0b0000_0001;
        const WhiteQueenside = 0b0000_0010;
        /// A mask for whether white can castle in either direction
        const White = 0b0000_0011;
        const BlackKingside = 0b0000_0100;
        const BlackQueenside = 0b0000_1000;
        /// A mask for whether black can castle in either direction
        const Black = 0b0000_1100;
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Traditional;
impl Variant for Traditional {
    type CastleState = TraditionalCastleOptions;

    const INITIAL_CASTLE_STATE: Self::CastleState = TraditionalCastleOptions::all();

    #[inline]
    fn update_castle_state(
        state: Self::CastleState,
        move_piece: Piece,
        source_square: BoardSquare,
        target_square: BoardSquare,
    ) -> Self::CastleState {
        // The piece being moved can't castle anymore
        let state = match move_piece {
            Piece {
                kind: PieceKind::King,
                color: Color::White,
            } => state & !TraditionalCastleOptions::White,
            Piece {
                kind: PieceKind::King,
                color: Color::Black,
            } => state & !TraditionalCastleOptions::Black,
            Piece {
                kind: PieceKind::Rook,
                color: Color::White,
            } => {
                if source_square == BoardSquare::A1 {
                    state & !TraditionalCastleOptions::WhiteQueenside
                } else if source_square == BoardSquare::H1 {
                    state & !TraditionalCastleOptions::WhiteKingside
                } else {
                    state
                }
            }
            Piece {
                kind: PieceKind::Rook,
                color: Color::Black,
            } => {
                if source_square == BoardSquare::A8 {
                    state & !TraditionalCastleOptions::BlackQueenside
                } else if source_square == BoardSquare::H8 {
                    state & !TraditionalCastleOptions::BlackKingside
                } else {
                    state
                }
            }
            _ => state,
        };
        match target_square {
            BoardSquare::A1 => state & !TraditionalCastleOptions::WhiteQueenside,
            BoardSquare::H1 => state & !TraditionalCastleOptions::WhiteKingside,
            BoardSquare::A8 => state & !TraditionalCastleOptions::BlackQueenside,
            BoardSquare::H8 => state & !TraditionalCastleOptions::BlackKingside,
            _ => state,
        }
    }

    #[inline]
    fn castle_state_to_fen(state: Self::CastleState) -> String {
        let mut options = String::with_capacity(4);
        if state.contains(TraditionalCastleOptions::WhiteKingside) {
            options.push('K');
        }
        if state.contains(TraditionalCastleOptions::WhiteQueenside) {
            options.push('Q');
        }
        if state.contains(TraditionalCastleOptions::BlackKingside) {
            options.push('k');
        }
        if state.contains(TraditionalCastleOptions::BlackQueenside) {
            options.push('q');
        }
        if options.is_empty() {
            options.push('-');
        }
        options
    }

    #[inline]
    fn castle_state_from_fen(mut fen: &str) -> Self::CastleState {
        let mut state = TraditionalCastleOptions::empty();
        if fen.get(0..1) == Some("K") {
            state |= TraditionalCastleOptions::WhiteKingside;
            fen = &fen[1..];
        }
        if fen.get(0..1) == Some("Q") {
            state |= TraditionalCastleOptions::WhiteQueenside;
            fen = &fen[1..];
        }
        if fen.get(0..1) == Some("k") {
            state |= TraditionalCastleOptions::BlackKingside;
            fen = &fen[1..];
        }
        if fen.get(0..1) == Some("q") {
            state |= TraditionalCastleOptions::BlackQueenside;
        }
        state
    }

    #[inline]
    fn is_castle_allowed(
        state: Self::CastleState,
        player: Color,
        kingside: bool,
    ) -> Option<Self::CastleState> {
        if state.contains(match (kingside, player) {
            (true, Color::White) => TraditionalCastleOptions::WhiteKingside,
            (false, Color::White) => TraditionalCastleOptions::WhiteQueenside,
            (true, Color::Black) => TraditionalCastleOptions::BlackKingside,
            (false, Color::Black) => TraditionalCastleOptions::BlackQueenside,
        }) {
            Some(
                state
                    & match player {
                        Color::White => !TraditionalCastleOptions::White,
                        Color::Black => !TraditionalCastleOptions::Black,
                    },
            )
        } else {
            None
        }
    }

    #[inline]
    fn initial_fen<'a>() -> &'a str {
        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
    }
}
