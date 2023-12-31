use core::str::FromStr;

use board::{
    AlgebraicNotationMove, AlgebraicNotationMoveType, Board, BoardSquare, CheckStatus, Color,
    GameOutcome, LongAlgebraicNotationMove, Piece, PieceKind,
};
use utils::{debug_impossible, debug_unreachable, UnreachableExpect};

pub mod bitboard;
mod detailed_move;

pub use crate::bitboard::Bitboard;
pub use crate::detailed_move::DetailedMove;

/// The bitboards representing a traditional chess board
pub type BitboardRepresentation = BitboardRepresentationInner<board::variants::Traditional>;

impl BitboardRepresentation {
    /// The state at the start of a normal chess game
    pub const INITIAL_STATE: Self = Self {
        white_pawn: Bitboard(0xFF00),
        white_rook: Bitboard(0x81),
        white_knight: Bitboard(0x42),
        white_bishop: Bitboard(0x24),
        white_queen: Bitboard(0x08),
        white_king: BoardSquare(0x04),
        black_pawn: Bitboard(0x00FF0000_00000000),
        black_rook: Bitboard(0x81000000_00000000),
        black_knight: Bitboard(0x42000000_00000000),
        black_bishop: Bitboard(0x24000000_00000000),
        black_queen: Bitboard(0x08000000_00000000),
        black_king: BoardSquare(0x74),
        en_passant_target: BoardSquare::INVALID,
        side_to_move: Color::White,
        castles: <board::variants::Traditional as board::variants::Variant>::INITIAL_CASTLE_STATE,
        halfmove_clock: 0,
        turn_counter: 1,
    };
}

pub type Result<T, E = Error> = core::result::Result<T, E>;

#[derive(Debug, thiserror::Error)]
pub enum AlgebraicNotationError {
    #[error("invalid algebraic notation given")]
    InvalidAlgebraicNotation,
    #[error("no source piece found for move")]
    NoSourcePiece,
    #[error("multiple source pieces found for move, but no disambiguation given")]
    AmbiguousSourcePiece,
}

#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    #[error("error getting move from algebraic notation: {0}")]
    InterpretAlgebraicNotationError(#[from] AlgebraicNotationError),
    #[error("given move never legal")]
    MoveNeverLegal,
    #[error("given move is blocked by another piece")]
    MoveBlocked,
    #[error("required piece not found at move source")]
    SourcePieceNotAtStart,
    #[error("attempted castle not allowed in current board state")]
    IllegalCastle,
    #[error("attempted en passant not allowed in current board state")]
    IllegalEnPassant,
    #[error("not attempted to capture, but enemy piece there")]
    NonCaptureTargetTaken,
    #[error("attempted to capture, but no piece there to be captured")]
    CaptureTargetMissing,
    #[error("attempted move puts moving side's king in check")]
    MovingIntoCheck,
    #[error("attempted castle with King in check")]
    CastleOutOfCheck,
    #[error("game has been drawn by 50 move rule")]
    SeventyFiveMoveRule,
    #[error("some other error")]
    Other,
}

/// Represent using a bunch of bitboards
///
/// This crate provides type aliases for different variants, which are recommended to be used
/// explicitly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitboardRepresentationInner<Variant: board::variants::Variant> {
    // piece placement
    pub white_pawn: Bitboard,
    pub white_rook: Bitboard,
    pub white_knight: Bitboard,
    pub white_bishop: Bitboard,
    pub white_queen: Bitboard,
    pub white_king: BoardSquare,
    pub black_pawn: Bitboard,
    pub black_rook: Bitboard,
    pub black_knight: Bitboard,
    pub black_bishop: Bitboard,
    pub black_queen: Bitboard,
    pub black_king: BoardSquare,

    // flags
    /// Whether en passant is allowed and, if so, where
    ///
    /// If no en passant is allowed, then this will be an invalid square
    pub en_passant_target: BoardSquare,
    pub side_to_move: Color,
    /// What castles are allowed, given the history of moves
    ///
    /// These castles aren't necessarily legal right now, as it may be blocked by intervening
    /// pieces and/or checks.
    pub castles: Variant::CastleState,

    // clocks
    /// Number of half-moves since pawn was moved or piece was captured
    ///
    /// Draw by 50 move rule when this counter hits 100
    pub halfmove_clock: u8,
    /// The number of turns elapsed in the game
    pub turn_counter: u16,
}

impl<Variant: board::variants::Variant> BitboardRepresentationInner<Variant> {
    /// A board with no pieces on it and no moves made
    pub const EMPTY: Self = Self {
        white_pawn: Bitboard::empty(),
        white_rook: Bitboard::empty(),
        white_knight: Bitboard::empty(),
        white_bishop: Bitboard::empty(),
        white_queen: Bitboard::empty(),
        white_king: BoardSquare::INVALID,
        black_pawn: Bitboard::empty(),
        black_rook: Bitboard::empty(),
        black_knight: Bitboard::empty(),
        black_bishop: Bitboard::empty(),
        black_queen: Bitboard::empty(),
        black_king: BoardSquare::INVALID,
        en_passant_target: BoardSquare::INVALID,
        side_to_move: Color::White,
        castles: Variant::INITIAL_CASTLE_STATE,
        halfmove_clock: 0,
        turn_counter: 0,
    };

    /// The squares occupied by white's pieces
    #[inline]
    pub const fn white_bitboard(&self) -> Bitboard {
        self.white_pawn
            .union(self.white_rook)
            .union(self.white_knight)
            .union(self.white_bishop)
            .union(self.white_queen)
            .union(Bitboard::from_board_square(self.white_king))
    }

    /// The squares occupied by black's pieces
    #[inline]
    pub const fn black_bitboard(&self) -> Bitboard {
        self.black_pawn
            .union(self.black_rook)
            .union(self.black_knight)
            .union(self.black_bishop)
            .union(self.black_queen)
            .union(Bitboard::from_board_square(self.black_king))
    }

    /// Returns a bitboard of all occupied squares
    #[inline]
    pub const fn bitboard_occupied(&self) -> Bitboard {
        self.white_bitboard().union(self.black_bitboard())
    }

    /// Find the piece, if any, at the given square
    ///
    /// Returns `None` if the given square is invalid.
    #[inline]
    pub fn get(&self, square: BoardSquare) -> Option<Piece> {
        if !square.is_valid() {
            return None;
        }
        if square == self.white_king {
            return Some(Piece {
                color: Color::White,
                kind: PieceKind::King,
            });
        }
        if square == self.black_king {
            return Some(Piece {
                color: Color::Black,
                kind: PieceKind::King,
            });
        }
        let query_bitboard = Bitboard::from(square);
        macro_rules! check {
            ($query:ident: $($field:ident => ($color:ident, $kind:ident),)*) => {$(if $query.intersects(self.$field) {
                return Some(Piece { color: Color::$color, kind: PieceKind::$kind, })
            })*};
        }
        check!(query_bitboard:
            white_pawn => (White, Pawn),
            white_rook => (White, Rook),
            white_knight => (White, Knight),
            white_bishop => (White, Bishop),
            white_queen => (White, Queen),
            black_pawn => (Black, Pawn),
            black_rook => (Black, Rook),
            black_knight => (Black, Knight),
            black_bishop => (Black, Bishop),
            black_queen => (Black, Queen),
        );
        None
    }

    /// Check if this move is legal to do right now.
    ///
    /// Returns `Ok(())` if the move is legal, otherwise `Err(..)` containing the reason why the
    /// move is illegal.
    #[inline]
    fn check_move_legality(&self, m: DetailedMove) -> Result<()> {
        if self.halfmove_clock >= 150 {
            // TODO Claim draw at 50 moves
            return Err(Error::SeventyFiveMoveRule);
        }
        let Some((own, other)) = m.legality_check() else {
            return Err(Error::MoveNeverLegal);
        };
        if !self
            .piece_bitboard(m.piece)
            .intersects(Bitboard::from(m.source))
        {
            return Err(Error::SourcePieceNotAtStart);
        }
        if m.is_castle && self.is_check(m.piece.color) {
            return Err(Error::CastleOutOfCheck);
        }
        match m.piece.color {
            Color::White => {
                if own.intersects(self.white_bitboard()) || other.intersects(self.black_bitboard())
                {
                    return Err(Error::MoveBlocked);
                }
            }
            Color::Black => {
                if own.intersects(self.black_bitboard()) || other.intersects(self.white_bitboard())
                {
                    return Err(Error::MoveBlocked);
                }
            }
        }
        if m.is_castle {
            let kingside = match m.target.to_rank_file() {
                Some((_, 6)) => true,
                Some((_, 2)) => false,
                _ => return Err(Error::IllegalCastle),
            };
            // Check that this castle hasn't been disallowed because we've moved the piece
            Variant::is_castle_allowed(self.castles, m.piece.color, kingside)
                .ok_or(Error::IllegalCastle)?;
        }
        if m.is_en_passant
            && !(self.en_passant_target.is_valid() && self.en_passant_target == m.target)
        {
            return Err(Error::IllegalEnPassant);
        }
        if m.is_capture
            && !m.is_en_passant
            && !match m.piece.color {
                Color::White => self.black_bitboard(),
                Color::Black => self.white_bitboard(),
            }
            .intersects(Bitboard::from(m.target))
        {
            return Err(Error::CaptureTargetMissing);
        }
        if !m.is_capture
            && match m.piece.color {
                Color::White => self.black_bitboard(),
                Color::Black => self.white_bitboard(),
            }
            .intersects(Bitboard::from(m.target))
        {
            return Err(Error::NonCaptureTargetTaken);
        }
        let mut post_move = self.clone();
        if m.piece.kind == PieceKind::King {
            if let Some(capture) = post_move.get(m.target) {
                *post_move.piece_bitboard_mut(capture) &= !Bitboard::from_board_square(m.target);
            }
            match m.piece.color {
                Color::White => post_move.white_king = m.target,
                Color::Black => post_move.black_king = m.target,
            }
        } else {
            *post_move.piece_bitboard_mut(m.piece) &= !Bitboard::from_board_square(m.source);
            if m.is_en_passant {
                *post_move.piece_bitboard_mut(Piece {
                    kind: PieceKind::Pawn,
                    color: self.side_to_move.other(),
                }) &= !Bitboard::from_board_square(self.en_passant_target.offset(
                    match self.side_to_move {
                        Color::White => -1,
                        Color::Black => 1,
                    },
                    0,
                ));
            } else if let Some(capture) = post_move.get(m.target) {
                debug_assert!(
                    capture.kind != PieceKind::King,
                    "Cannot ever capture a king"
                );
                *post_move.piece_bitboard_mut(capture) &= !Bitboard::from_board_square(m.target);
            }
            *post_move.piece_bitboard_mut(m.piece) |= Bitboard::from_board_square(m.target);
        }
        if post_move.is_check(self.side_to_move) {
            return Err(Error::MovingIntoCheck);
        }
        Ok(())
    }

    /// Do the move without checking if it's legal
    ///
    /// # Safety
    /// There's some `unreachable_unchecked` in here, if the move isn't legal.
    #[inline]
    pub unsafe fn do_move(&mut self, m: DetailedMove) {
        match (m.piece.kind, m.piece.color) {
            (PieceKind::King, Color::White) => {
                if m.is_castle {
                    if m.target == BoardSquare::C1 {
                        self.white_rook &= !Bitboard::from_board_square(BoardSquare::A1);
                        self.white_rook |= BoardSquare::D1;
                        self.castles =
                            Variant::is_castle_allowed(self.castles, Color::White, false)
                                .expect_unreachable("Did illegal castle");
                    } else if m.target == BoardSquare::G1 {
                        self.white_rook &= !Bitboard::from_board_square(BoardSquare::H1);
                        self.white_rook |= BoardSquare::F1;
                        self.castles = Variant::is_castle_allowed(self.castles, Color::White, true)
                            .expect_unreachable("Did illegal castle");
                    } else {
                        debug_unreachable!("Castle with illegal target");
                    }
                } else {
                    if m.is_capture {
                        if m.is_castle {
                            debug_unreachable!("capture and castle together");
                        }
                        if let Some(piece) = self.get(m.target) {
                            *self.piece_bitboard_mut(piece) &=
                                !Bitboard::from_board_square(m.target);
                        } else {
                            debug_unreachable!("Capture move without target piece");
                        }
                    }
                    self.castles =
                        Variant::update_castle_state(self.castles, m.piece, m.source, m.target);
                }
                debug_impossible!(m.is_en_passant, "Can't en passant with a king");
                debug_impossible!(m.promotion_into.is_some(), "Can't promote a king");
                self.white_king = m.target;
            }
            (PieceKind::King, Color::Black) => {
                if m.is_castle {
                    if m.target == BoardSquare::C8 {
                        self.black_rook &= !Bitboard::from_board_square(BoardSquare::A8);
                        self.black_rook |= BoardSquare::D8;
                        self.castles =
                            Variant::is_castle_allowed(self.castles, Color::Black, false)
                                .expect_unreachable("Did illegal castle");
                    } else if m.target == BoardSquare::G8 {
                        self.black_rook &= !Bitboard::from_board_square(BoardSquare::H8);
                        self.black_rook |= BoardSquare::F8;
                        self.castles = Variant::is_castle_allowed(self.castles, Color::Black, true)
                            .expect_unreachable("Did illegal castle");
                    } else {
                        debug_unreachable!("Castle with illegal target");
                    }
                } else {
                    if m.is_capture {
                        if m.is_castle {
                            debug_unreachable!("capture and castle together");
                        }
                        if let Some(piece) = self.get(m.target) {
                            *self.piece_bitboard_mut(piece) &=
                                !Bitboard::from_board_square(m.target);
                        } else {
                            debug_unreachable!("Capture move without target piece");
                        }
                    }
                    self.castles =
                        Variant::update_castle_state(self.castles, m.piece, m.source, m.target);
                }
                debug_impossible!(m.is_en_passant, "Can't en passant with a king");
                debug_impossible!(m.promotion_into.is_some(), "Can't promote a king");
                self.black_king = m.target;
            }
            _ => {
                *self.piece_bitboard_mut(m.piece) &=
                    Bitboard::from_board_square(m.source).negation();
                if m.is_en_passant {
                    let (target_rank, target_file) = m
                        .target
                        .to_rank_file()
                        .expect_unreachable("Move target was invalid square");
                    let clear_bitboard = Bitboard::from_board_square(match m.piece.color {
                        Color::White => BoardSquare::from_rank_file(target_rank - 1, target_file),
                        Color::Black => BoardSquare::from_rank_file(target_rank + 1, target_file),
                    });
                    *self.piece_bitboard_mut(Piece {
                        kind: PieceKind::Pawn,
                        color: m.piece.color.other(),
                    }) &= !clear_bitboard;
                } else if m.is_capture {
                    if let Some(piece) = self.get(m.target) {
                        *self.piece_bitboard_mut(piece) &= !Bitboard::from_board_square(m.target);
                    } else {
                        debug_unreachable!("Capture move without target piece");
                    }
                }
                if m.piece.kind != PieceKind::Pawn {
                    debug_impossible!(m.promotion_into.is_some(), "Can't promote a non-pawn");
                }
                if let Some(promote) = m.promotion_into {
                    debug_impossible!(
                        !promote.is_promotable(),
                        "Can't promote into a pawn or king"
                    );
                }
                *self.piece_bitboard_mut(Piece {
                    kind: m.promotion_into.unwrap_or(m.piece.kind),
                    color: m.piece.color,
                }) |= Bitboard::from(m.target);
            }
        }
        self.side_to_move = self.side_to_move.other();
        if self.side_to_move == Color::White {
            self.turn_counter += 1;
        }
        self.castles = Variant::update_castle_state(self.castles, m.piece, m.source, m.target);
        if m.is_capture || m.piece.kind == PieceKind::Pawn {
            self.halfmove_clock = 0;
        } else {
            self.halfmove_clock += 1;
        }
        self.en_passant_target = m.en_passant_response();
    }

    /// If the given move is legal, then do it.
    ///
    /// Otherwise, this method returns `Err(..)` with why the move is illegal.
    #[inline]
    pub fn do_move_if_legal(&mut self, m: DetailedMove) -> Result<()> {
        self.check_move_legality(m)?;
        // SAFETY:
        // We just checked if the move is legal
        unsafe { self.do_move(m) };
        Ok(())
    }

    /// Convert the given algebraic notation into the format we use
    ///
    /// This uses the current board state to disambiguate a lot of things which are left ambiguous
    /// in default algebraic notation.
    #[inline]
    pub fn detail_algebraic_move(
        &self,
        m: AlgebraicNotationMove,
    ) -> Result<DetailedMove, AlgebraicNotationError> {
        Ok(match m.move_type {
            AlgebraicNotationMoveType::CastleKingside => {
                let (source, target) = match self.side_to_move {
                    Color::White => (BoardSquare::E1, BoardSquare::G1),
                    Color::Black => (BoardSquare::E8, BoardSquare::G8),
                };
                DetailedMove {
                    piece: Piece {
                        kind: PieceKind::King,
                        color: self.side_to_move,
                    },
                    source,
                    target,
                    is_castle: true,
                    is_en_passant: false,
                    is_capture: false,
                    promotion_into: None,
                }
            }
            AlgebraicNotationMoveType::CastleQueenside => {
                let (source, target) = match self.side_to_move {
                    Color::White => (BoardSquare::E1, BoardSquare::C1),
                    Color::Black => (BoardSquare::E8, BoardSquare::C8),
                };
                DetailedMove {
                    piece: Piece {
                        kind: PieceKind::King,
                        color: self.side_to_move,
                    },
                    source,
                    target,
                    is_castle: true,
                    is_en_passant: false,
                    is_capture: false,
                    promotion_into: None,
                }
            }
            AlgebraicNotationMoveType::Normal(board::AlgebraicNotationNormalMove {
                kind: PieceKind::King,
                from_file,
                from_rank,
                capture,
                to_square,
                promotion,
            }) => {
                // None of these should ever be set for this piece
                debug_assert!(from_file.is_none());
                debug_assert!(from_rank.is_none());
                debug_assert!(promotion.is_none());
                DetailedMove {
                    piece: Piece {
                        kind: PieceKind::King,
                        color: self.side_to_move,
                    },
                    source: self.king_square(self.side_to_move),
                    target: to_square,
                    is_castle: false,
                    is_en_passant: false,
                    is_capture: capture,
                    promotion_into: None,
                }
            }
            AlgebraicNotationMoveType::Normal(board::AlgebraicNotationNormalMove {
                kind,
                from_file,
                from_rank,
                capture,
                to_square,
                promotion,
            }) => {
                let piece = Piece {
                    kind,
                    color: self.side_to_move,
                };
                let from_file = from_file.map(|from_file| (from_file as u32 - 'a' as u32) as u8);
                let from_rank = from_rank.map(|from_rank| from_rank - 1);
                let is_en_passant =
                    self.en_passant_target == to_square && capture && kind == PieceKind::Pawn;
                let source = match (from_file, from_rank) {
                    (Some(file), Some(rank)) => BoardSquare::from_rank_file(rank, file),
                    _ => {
                        let mut pieces_iter =
                            self.piece_bitboard(piece).squares_iter().filter(|square| {
                                let Some((rank, file)) = square.to_rank_file() else {
                                    return false;
                                };
                                if from_rank.is_some_and(|r| rank != r) {
                                    return false;
                                }
                                if from_file.is_some_and(|f| file != f) {
                                    return false;
                                }
                                let Some((target_rank, target_file)) = to_square.to_rank_file() else {
                                    return false;
                                };
                                // Check that the move is legal for the kind of piece
                                match (kind, self.side_to_move) {
                                    (PieceKind::Pawn, Color::White) => {
                                        if capture {
                                            if target_rank.saturating_sub(rank) != 1 {
                                                return false;
                                            }
                                            target_file.abs_diff(file) == 1
                                        } else {
                                            if target_file != file {
                                                return false;
                                            }
                                            if target_rank.checked_sub(rank) == Some(1) {
                                                true
                                            } else if target_rank == 3 && rank == 1 {
                                                // Double pawn move only if the middle square is
                                                // clear
                                                self.get(BoardSquare::from_rank_file(2, file)).is_none()
                                            } else {
                                                false
                                            }
                                        }
                                    }
                                    (PieceKind::Pawn, Color::Black) => {
                                        if capture {
                                            if rank.saturating_sub(target_rank) != 1 {
                                                return false;
                                            }
                                            target_file.abs_diff(file) == 1
                                        } else {
                                            if target_file != file {
                                                return false;
                                            }
                                            if rank.checked_sub(target_rank) == Some(1) {
                                                true
                                            } else if target_rank == 4 && rank == 6 {
                                                // Double pawn move only if the middle square is
                                                // clear
                                                self.get(BoardSquare::from_rank_file(5, file)).is_none()
                                            } else {
                                                false
                                            }
                                        }
                                    }
                                    (PieceKind::Rook, _) => {
                                        (rank == target_rank || file == target_file)
                                            && !self.bitboard_occupied().intersects(Bitboard::rook_move_middle(*square, to_square))
                                    },
                                    (PieceKind::Knight, _) => {
                                        rank.abs_diff(target_rank) == 2
                                            && file.abs_diff(target_file) == 1
                                            || rank.abs_diff(target_rank) == 1
                                                && file.abs_diff(target_file) == 2
                                    }
                                    (PieceKind::Bishop, _) => {
                                        rank.abs_diff(target_rank) == file.abs_diff(target_file)
                                            && !self.bitboard_occupied().intersects(Bitboard::bishop_move_middle(*square, to_square))
                                    },
                                    (PieceKind::Queen, _) => {
                                        if rank == target_rank || file == target_file {
                                            !self.bitboard_occupied().intersects(Bitboard::rook_move_middle(*square, to_square))
                                        } else if rank.abs_diff(target_rank) == file.abs_diff(target_file) {
                                            !self.bitboard_occupied().intersects(Bitboard::bishop_move_middle(*square, to_square))
                                        } else {
                                            false
                                        }
                                    }
                                    (PieceKind::King, _) => {
                                        rank.abs_diff(target_rank) <= 1
                                            && file.abs_diff(target_file) <= 1
                                    }
                                }
                            })
                            // Check if the move is putting us in check
                            .filter(|square| {
                                // Check that we aren't moving into check
                                let mut post_move = self.clone();
                                *post_move.piece_bitboard_mut(piece) &= !Bitboard::from_board_square(*square);
                                if is_en_passant {
                                    *post_move.piece_bitboard_mut(Piece { kind: PieceKind::Pawn, color: self.side_to_move.other() })
                                        &= !Bitboard::from_board_square(
                                            self.en_passant_target.offset(
                                                match self.side_to_move {
                                                    Color::White => -1,
                                                    Color::Black => 1
                                                },
                                                0
                                                )
                                            );
                                } else if let Some(capture) = post_move.get(to_square) {
                                    *post_move.piece_bitboard_mut(capture) &= !Bitboard::from_board_square(to_square);
                                }
                                *post_move.piece_bitboard_mut(piece) |= Bitboard::from_board_square(to_square);
                                !post_move.is_check(self.side_to_move)
                            });
                        let Some(source) = pieces_iter.next() else {
                            // We didn't find a piece
                            return Err(AlgebraicNotationError::NoSourcePiece);
                        };
                        if pieces_iter.next().is_some() {
                            // This was ambiguous
                            return Err(AlgebraicNotationError::AmbiguousSourcePiece);
                        }
                        source
                    }
                };
                DetailedMove {
                    piece,
                    source,
                    target: to_square,
                    promotion_into: promotion,
                    is_capture: capture,
                    is_castle: false,
                    is_en_passant,
                }
            }
        })
    }

    #[inline]
    pub fn detail_long_algebraic_move(
        &self,
        mv: LongAlgebraicNotationMove,
    ) -> Result<DetailedMove, AlgebraicNotationError> {
        let piece = self
            .get(mv.source)
            .ok_or(AlgebraicNotationError::NoSourcePiece)?;
        let is_castle = piece.kind == PieceKind::King
            && mv.source.offset_to(mv.target).chebyshev_distance() >= 2;
        let is_en_passant = piece.kind == PieceKind::Pawn
            && mv.target == self.en_passant_target
            && self.en_passant_target.is_valid();
        let is_capture = is_en_passant
            || self.get(mv.target).map_or(false, |target_piece| {
                target_piece.color == piece.color.other()
            });
        Ok(DetailedMove {
            piece,
            source: mv.source,
            target: mv.target,
            promotion_into: mv.promotion,
            is_capture,
            is_castle,
            is_en_passant,
        })
    }

    /// Get the square on which the given player's King resides
    #[inline]
    pub const fn king_square(&self, color: Color) -> BoardSquare {
        match color {
            Color::White => self.white_king,
            Color::Black => self.black_king,
        }
    }

    /// Get the bitboard associated with the given piece
    #[inline]
    pub const fn piece_bitboard(&self, piece: Piece) -> Bitboard {
        match (piece.kind, piece.color) {
            (PieceKind::Pawn, Color::White) => self.white_pawn,
            (PieceKind::Rook, Color::White) => self.white_rook,
            (PieceKind::Knight, Color::White) => self.white_knight,
            (PieceKind::Bishop, Color::White) => self.white_bishop,
            (PieceKind::Queen, Color::White) => self.white_queen,
            (PieceKind::King, Color::White) => Bitboard::from_board_square(self.white_king),
            (PieceKind::Pawn, Color::Black) => self.black_pawn,
            (PieceKind::Rook, Color::Black) => self.black_rook,
            (PieceKind::Knight, Color::Black) => self.black_knight,
            (PieceKind::Bishop, Color::Black) => self.black_bishop,
            (PieceKind::Queen, Color::Black) => self.black_queen,
            (PieceKind::King, Color::Black) => Bitboard::from_board_square(self.black_king),
        }
    }

    /// Get a mutable reference to the bitboard associated with the given piece
    ///
    /// This can't be called on [`PieceKind::King`] because we don't store the bitboard when we can
    /// only have one piece.
    #[inline]
    pub fn piece_bitboard_mut(&mut self, piece: Piece) -> &mut Bitboard {
        match (piece.kind, piece.color) {
            (PieceKind::King, _) => panic!("No king bitboard exists"),
            (PieceKind::Pawn, Color::White) => &mut self.white_pawn,
            (PieceKind::Rook, Color::White) => &mut self.white_rook,
            (PieceKind::Knight, Color::White) => &mut self.white_knight,
            (PieceKind::Bishop, Color::White) => &mut self.white_bishop,
            (PieceKind::Queen, Color::White) => &mut self.white_queen,
            (PieceKind::Pawn, Color::Black) => &mut self.black_pawn,
            (PieceKind::Rook, Color::Black) => &mut self.black_rook,
            (PieceKind::Knight, Color::Black) => &mut self.black_knight,
            (PieceKind::Bishop, Color::Black) => &mut self.black_bishop,
            (PieceKind::Queen, Color::Black) => &mut self.black_queen,
        }
    }

    /// Returns the bitboard of all squares threatened by the given player
    ///
    /// Note that a square is considered threatened if the given player can move a piece onto that
    /// square on that player's next turn. This is exactly equal to the set of squares onto which
    /// the opposing player can not move their king.
    ///
    /// # Edge cases:
    /// * A piece is not considered to threaten the square that it is on
    /// * Pieces are considered to threaten a square which contains a friendly piece but which they
    ///   could otherwise move onto.
    /// * Kings are not considered to block moves.
    #[inline]
    pub fn threatened_squares(&self, color: Color) -> Bitboard {
        let blockers = self.bitboard_occupied()
            & !Bitboard::from_board_square(self.king_square(color.other()));
        let mut threatened_squares = Bitboard::king_moves(self.king_square(color));
        for piece_kind in PieceKind::KINDS {
            let piece = Piece {
                kind: piece_kind,
                color,
            };
            threatened_squares = threatened_squares.union(
                self.piece_bitboard(piece)
                    .squares_threatened(piece, blockers),
            );
        }
        threatened_squares
    }

    /// A fast function which checks whether we're in check, but may return `true` if the answer is
    /// `false`.
    ///
    /// This function exists as a hint to speed up `is_check`, which is slow and called a lot.
    #[inline]
    const fn quick_check_heuristic(&self, color: Color) -> bool {
        let king = self.king_square(color);
        Bitboard::containing_rank(king)
            .union(Bitboard::containing_file(king))
            .intersects(
                self.piece_bitboard(Piece {
                    kind: PieceKind::Rook,
                    color: color.other(),
                })
                .union(self.piece_bitboard(Piece {
                    kind: PieceKind::Queen,
                    color: color.other(),
                })),
            )
            || Bitboard::containing_diagonals(king).intersects(
                self.piece_bitboard(Piece {
                    kind: PieceKind::Bishop,
                    color: color.other(),
                })
                .union(self.piece_bitboard(Piece {
                    kind: PieceKind::Queen,
                    color: color.other(),
                })),
            )
            || Bitboard::knight_moves(king).intersects(self.piece_bitboard(Piece {
                kind: PieceKind::Knight,
                color: color.other(),
            }))
            || match color {
                Color::White => self.black_pawn.intersects(
                    Bitboard::from_board_square(king.offset(1, 1))
                        .union(Bitboard::from_board_square(king.offset(1, -1))),
                ),
                Color::Black => self.white_pawn.intersects(
                    Bitboard::from_board_square(king.offset(-1, 1))
                        .union(Bitboard::from_board_square(king.offset(-1, -1))),
                ),
            }
            || self
                .white_king
                .offset_to(self.black_king)
                .chebyshev_distance()
                == 1
    }

    /// Returns `true` if the given color's King is in check
    #[inline]
    fn is_check(&self, color: Color) -> bool {
        if self.halfmove_clock >= 150 {
            // Can't be in check if the game has been drawn
            return false;
        }
        if !self.quick_check_heuristic(color) {
            return false;
        }
        self.threatened_squares(color.other())
            .contains(Bitboard::from_board_square(self.king_square(color)))
    }

    /// Returns `true` if the given color's King is in checkmate
    #[inline]
    fn is_checkmate(&self) -> bool {
        self.is_check(self.side_to_move) && self.legal_moves().next().is_none()
    }

    /// Returns the list of legal moves for the given player
    #[inline]
    pub fn legal_moves(&self) -> impl Iterator<Item = DetailedMove> + '_ {
        let color = self.side_to_move;
        let own_pieces = match color {
            Color::White => self.white_bitboard(),
            Color::Black => self.black_bitboard(),
        };
        let enemy_pieces = match color {
            Color::White => self.black_bitboard(),
            Color::Black => self.white_bitboard(),
        };
        own_pieces
            .squares_iter()
            .flat_map(move |source| {
                let piece = self.get(source).expect_unreachable("Empty source piece");
                let possible_targets = match (piece.kind, piece.color) {
                    (PieceKind::Rook, _) => {
                        Bitboard::containing_rank(source) | Bitboard::containing_file(source)
                    }
                    (PieceKind::Knight, _) => Bitboard::knight_moves(source),
                    (PieceKind::Bishop, _) => Bitboard::containing_diagonals(source),
                    (PieceKind::Queen, _) => {
                        Bitboard::containing_diagonals(source)
                            | Bitboard::containing_rank(source)
                            | Bitboard::containing_file(source)
                    }
                    (PieceKind::King, _) => Bitboard::king_moves_with_castling(source),
                    (PieceKind::Pawn, Color::White) => {
                        let (source_rank, source_file) = source
                            .to_rank_file()
                            .expect_unreachable("Invalid source square");
                        let normal = Bitboard::from_board_square(BoardSquare::from_rank_file(
                            source_rank + 1,
                            source_file,
                        ));
                        let with_captures = normal
                            | (Bitboard::from_board_square(BoardSquare::from_rank_file(
                                source_rank + 1,
                                source_file.wrapping_sub(1),
                            )) | Bitboard::from_board_square(BoardSquare::from_rank_file(
                                source_rank + 1,
                                source_file + 1,
                            ))) & (enemy_pieces
                                | Bitboard::from_board_square(self.en_passant_target));
                        if source_rank == 1 {
                            with_captures
                                | Bitboard::from_board_square(BoardSquare::from_rank_file(
                                    3,
                                    source_file,
                                ))
                        } else {
                            with_captures
                        }
                    }
                    (PieceKind::Pawn, Color::Black) => {
                        let (source_rank, source_file) = source
                            .to_rank_file()
                            .expect_unreachable("Invalid source square");
                        let normal = Bitboard::from_board_square(BoardSquare::from_rank_file(
                            source_rank - 1,
                            source_file,
                        ));
                        let with_captures = normal
                            | (Bitboard::from_board_square(BoardSquare::from_rank_file(
                                source_rank - 1,
                                source_file.wrapping_sub(1),
                            )) | Bitboard::from_board_square(BoardSquare::from_rank_file(
                                source_rank - 1,
                                source_file + 1,
                            ))) & (enemy_pieces
                                | Bitboard::from_board_square(self.en_passant_target));
                        if source_rank == 6 {
                            with_captures
                                | Bitboard::from_board_square(BoardSquare::from_rank_file(
                                    4,
                                    source_file,
                                ))
                        } else {
                            with_captures
                        }
                    }
                };
                possible_targets.squares_iter().map(move |target| {
                    let is_en_passant =
                        target == self.en_passant_target && piece.kind == PieceKind::Pawn;
                    DetailedMove {
                        piece,
                        source,
                        target,
                        is_castle: piece.kind == PieceKind::King
                            && source.offset_to(target).chebyshev_distance() == 2,
                        is_en_passant,
                        is_capture: is_en_passant
                            || enemy_pieces.contains(Bitboard::from_board_square(target)),
                        promotion_into: None,
                    }
                })
            })
            .flat_map(move |mv| {
                // Add all the options for promoting a pawn
                let (target_rank, _) = mv
                    .target
                    .to_rank_file()
                    .expect_unreachable("Made move with invalid target");
                if mv.piece.kind == PieceKind::Pawn
                    && (mv.piece.color == Color::White && target_rank == 7
                        || mv.piece.color == Color::Black && target_rank == 0)
                {
                    &[
                        Some(PieceKind::Rook),
                        Some(PieceKind::Knight),
                        Some(PieceKind::Knight),
                        Some(PieceKind::Queen),
                    ][..]
                } else {
                    &[None][..]
                }
                .iter()
                .map(move |&promotion| {
                    let mut promoting = mv;
                    promoting.promotion_into = promotion;
                    promoting
                })
            })
            .filter(|&mv| self.check_move_legality(mv).is_ok())
    }

    /// Convert the given move back into algebraic notation
    ///
    /// ```
    /// use std::str::FromStr;
    /// use board::{Board, Color, PieceKind, Piece, BoardSquare, AlgebraicNotationMove};
    /// use bitboard::{BitboardRepresentation, DetailedMove};
    ///
    /// let board = BitboardRepresentation::from_fen(
    ///     "r6r/pp1k2p1/2p3p1/8/8/2PPP1bP/PP1K2P1/R6R b - - 2 21"
    /// );
    /// let algebraic = board.move_to_algebraic(DetailedMove {
    ///             piece: Piece {
    ///                 kind: PieceKind::Rook,
    ///                 color: Color::Black,
    ///             },
    ///             source: BoardSquare::A8,
    ///             target: BoardSquare::F8,
    ///             is_castle: false,
    ///             is_en_passant: false,
    ///             is_capture: false,
    ///             promotion_into: None,
    ///         });
    /// assert_eq!(
    ///     algebraic,
    ///     AlgebraicNotationMove::from_str("Raf8").unwrap(),
    ///     "was {algebraic}, expected Raf8",
    /// );
    /// ```
    #[inline]
    pub fn move_to_algebraic(&self, mv: DetailedMove) -> AlgebraicNotationMove {
        let check = {
            let mut next = self.clone();
            if let Ok(()) = next.do_move_if_legal(mv) {
                next.check_status()
            } else {
                CheckStatus::None
            }
        };
        let move_type = if mv.is_castle {
            match mv.target.to_rank_file() {
                Some((_, 2)) => AlgebraicNotationMoveType::CastleQueenside,
                Some((_, 6)) => AlgebraicNotationMoveType::CastleKingside,
                _ => unreachable!(),
            }
        } else {
            let (from_rank, from_file) = mv.source.to_rank_file().expect("Invalid move target");
            // Adjust from the internal representation to algebraic notation
            let from_rank = from_rank + 1;
            let from_file = char::from_u32('a' as u32 + from_file as u32)
                .expect_unreachable("Valid move target with invalid file number");
            // Decide which of initial rank and file are necessary for disambiguation
            let ambiguous = self.piece_bitboard(mv.piece).squares_iter().any(|sq| {
                let other_mv = DetailedMove { source: sq, ..mv };
                sq != mv.source && self.check_move_legality(other_mv).is_ok()
            });
            let (from_rank, from_file) = if ambiguous {
                let same_rank = self
                    .piece_bitboard(mv.piece)
                    .intersection(Bitboard::containing_rank(mv.source))
                    .intersection(!Bitboard::from_board_square(mv.source))
                    .squares_iter()
                    .any(|sq| {
                        let other_mv = DetailedMove { source: sq, ..mv };
                        self.check_move_legality(other_mv).is_ok()
                    });
                let same_file = self
                    .piece_bitboard(mv.piece)
                    .intersection(Bitboard::containing_file(mv.source))
                    .intersection(!Bitboard::from_board_square(mv.source))
                    .squares_iter()
                    .any(|sq| {
                        let other_mv = DetailedMove { source: sq, ..mv };
                        self.check_move_legality(other_mv).is_ok()
                    });
                match (same_rank, same_file) {
                    (true, true) => (Some(from_rank), Some(from_file)),
                    (false, true) => (Some(from_rank), None),
                    (true, false) | (false, false) => (None, Some(from_file)),
                }
            } else if mv.piece.kind == PieceKind::Pawn && mv.is_capture {
                // Pawn captures always include the source file, even if not ambiguous
                (None, Some(from_file))
            } else {
                (None, None)
            };
            // Move everything to the right place
            AlgebraicNotationMoveType::Normal(board::AlgebraicNotationNormalMove {
                to_square: mv.target,
                kind: mv.piece.kind,
                capture: mv.is_capture,
                promotion: mv.promotion_into,
                from_file,
                from_rank,
            })
        };
        AlgebraicNotationMove { move_type, check }
    }
}

impl<Variant: board::variants::Variant> Board for BitboardRepresentationInner<Variant> {
    type Err = Error;

    #[inline]
    fn to_fen(&self) -> String {
        let pieces = {
            let bitboard_occupied = self.bitboard_occupied();
            let rows = (0..=7)
                .map(|row_idx| {
                    let row_idx = 7 - row_idx;
                    if bitboard_occupied.0 & (0xFF << (row_idx * 8)) == 0 {
                        return "8".to_string();
                    }
                    let mut positions = String::with_capacity(8);
                    let mut last_piece_file_idx = -1;
                    for file_idx in 0..8 {
                        let position = BoardSquare::from_rank_file(row_idx, file_idx);
                        if let Some(piece) = self.get(position) {
                            let squares_skipped = file_idx as i16 - last_piece_file_idx;
                            if squares_skipped > 1 {
                                positions.push(
                                    char::from_digit(squares_skipped as u32 - 1, 10).unwrap(),
                                );
                            }
                            positions.push(piece.fen_letter());
                            last_piece_file_idx = file_idx as i16;
                        }
                    }
                    if last_piece_file_idx != 7 {
                        positions
                            .push(char::from_digit(7 - last_piece_file_idx as u32, 10).unwrap());
                    }
                    positions
                })
                .collect::<Vec<String>>();
            rows.join("/")
        };
        let side_to_move = match self.side_to_move {
            Color::White => "w",
            Color::Black => "b",
        };
        let castling = Variant::castle_state_to_fen(self.castles);
        let en_passant_target = self.en_passant_target.as_str_legal().unwrap_or("-");
        let halfmove_clock = self.halfmove_clock;
        let fullmove_coutner = self.turn_counter;
        format!("{pieces} {side_to_move} {castling} {en_passant_target} {halfmove_clock} {fullmove_coutner}")
    }

    #[inline]
    fn from_fen(fen: &str) -> Self {
        let mut board = Self::EMPTY;
        let mut terms = fen.split(' ');
        {
            let pieces = terms.next().expect("Error parsing FEN");
            for (rank_idx, rank) in pieces.split('/').enumerate() {
                let rank_idx = 7 - rank_idx;
                if rank == "8" {
                    continue;
                }
                let mut file = 0;
                for c in rank.chars() {
                    if let Some(value) = c.to_digit(10) {
                        file += value as usize;
                        continue;
                    };
                    *match c {
                        'K' => {
                            board.white_king =
                                BoardSquare::from_rank_file(rank_idx as u8, file as u8);
                            file += 1;
                            continue;
                        }
                        'k' => {
                            board.black_king =
                                BoardSquare::from_rank_file(rank_idx as u8, file as u8);
                            file += 1;
                            continue;
                        }
                        'P' => &mut board.white_pawn,
                        'R' => &mut board.white_rook,
                        'N' => &mut board.white_knight,
                        'B' => &mut board.white_bishop,
                        'Q' => &mut board.white_queen,
                        'p' => &mut board.black_pawn,
                        'r' => &mut board.black_rook,
                        'n' => &mut board.black_knight,
                        'b' => &mut board.black_bishop,
                        'q' => &mut board.black_queen,
                        _ => panic!("Error parsing FEN"),
                    } |= Bitboard(1 << (rank_idx * 8 + file));
                    file += 1;
                }
            }
        }
        {
            let side_to_move = terms.next().expect("Error parsing FEN");
            board.side_to_move = match side_to_move {
                "w" => Color::White,
                "b" => Color::Black,
                _ => panic!("Error parsing fen"),
            };
        }
        board.castles = Variant::castle_state_from_fen(terms.next().expect("Error parsing FEN"));
        {
            let en_passant = terms.next().expect("Error parsing FEN");
            board.en_passant_target = if en_passant == "-" {
                BoardSquare::INVALID
            } else {
                BoardSquare::from_str(en_passant).expect("Error parsing FEN")
            };
        }
        {
            let halfmove = terms.next().expect("Error parsing FEN");
            board.halfmove_clock = halfmove.parse().expect("Error parsing FEN");
        }
        {
            let fullmove = terms.next().expect("Error parsing FEN");
            board.turn_counter = fullmove.parse().expect("Error parsing FEN");
        }
        board
    }

    #[inline]
    fn initial_state() -> Self {
        Self::from_fen(Variant::initial_fen())
    }

    #[inline]
    fn make_move(&mut self, mv: AlgebraicNotationMove) -> Result<()> {
        let mv = self.detail_algebraic_move(mv)?;
        self.do_move_if_legal(mv)
    }

    #[inline]
    fn make_long_move(
        &mut self,
        mv: LongAlgebraicNotationMove,
    ) -> std::result::Result<(), Self::Err> {
        let mv = self.detail_long_algebraic_move(mv)?;
        self.do_move_if_legal(mv)
    }

    #[inline]
    fn check_status(&self) -> CheckStatus {
        match (self.is_check(self.side_to_move), self.is_checkmate()) {
            (false, _) => CheckStatus::None,
            (true, false) => CheckStatus::Check,
            (true, true) => CheckStatus::Checkmate,
        }
    }

    #[inline]
    fn game_outcome(&self) -> board::GameOutcome {
        if self.halfmove_clock >= 150 {
            // 75-move rule
            GameOutcome::Draw
        } else if self.is_checkmate() {
            // Checkmate
            GameOutcome::Won(self.side_to_move.other())
        } else if self.legal_moves().next().is_none() {
            // Stalemate
            GameOutcome::Draw
        } else {
            // No loss has been hit, so keep going
            GameOutcome::InProgress
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use games_database::lichess_jan_2013_database;

    /// Ensure we don't increase the size on accident
    #[test]
    fn test_bitboard_size() {
        assert_eq!(core::mem::size_of::<BitboardRepresentation>(), 11 * 8);
    }

    #[test]
    fn test_opening_position_fen_parsing() {
        assert_eq!(
            BitboardRepresentation::INITIAL_STATE,
            BitboardRepresentation::from_fen(
                "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
            )
        );
    }

    #[test]
    fn test_opening_position_to_fen() {
        assert_eq!(
            BitboardRepresentation::INITIAL_STATE.to_fen(),
            "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
        );
    }

    /// Play all the moves in the first 10k games in the dataset
    ///
    /// This just checks that all the moves are still legal, but if we do anything wrong, odds are
    /// some future move will show up as wrong.
    #[test]
    fn test_against_lichess_jan_2013() {
        let mut failure_count = 0;
        let mut games_played = 0;
        'gameloop: for game in &lichess_jan_2013_database()[..10_000] {
            if failure_count >= 10 {
                eprintln!("Giving up after 10 failures :(");
                break 'gameloop;
            }
            games_played += 1;
            let mut board = BitboardRepresentation::initial_state();
            for mv in &game.moves {
                let board_copy = board.clone();
                board = match std::panic::catch_unwind(move || {
                    board.make_move(mv.notated)?;
                    Ok::<_, Error>(board)
                }) {
                    Ok(Ok(board)) => board,
                    Err(_) => {
                        failure_count += 1;
                        eprintln!(
                            "Caught panic in game {}:\nIn move `{}` from board: {}\n",
                            game.identifier,
                            mv.notated,
                            board_copy.to_fen()
                        );
                        continue 'gameloop;
                    }
                    Ok(Err(e)) => {
                        failure_count += 1;
                        eprintln!(
                            "Error in game {}:\n\t{e}\nin move `{}` from board: {}\n",
                            game.identifier,
                            mv.notated,
                            board_copy.to_fen()
                        );
                        continue 'gameloop;
                    }
                };
                let Ok(computed_check) = std::panic::catch_unwind(|| board.check_status()) else {
                    failure_count += 1;
                    eprintln!(
                        "Panic while computing if board is check\nin game {}:\nIn move `{}` from board: {}\n",
                        game.identifier,
                        mv.notated,
                        board.to_fen(),
                    );
                    continue 'gameloop;
                };
                if mv.notated.check != computed_check {
                    failure_count += 1;
                    eprintln!(
                        "Mismatched check status in game {}:\n\tWas {:?}\n\tComputed {:?}\n on board: {}\n",
                        game.identifier,
                        mv.notated.check,
                        computed_check,
                        board.to_fen()
                    );
                    eprintln!(
                        "White's threatened squares:\n{}",
                        board.threatened_squares(Color::White)
                    );
                    eprintln!(
                        "Black's threatened squares:\n{}",
                        board.threatened_squares(Color::Black)
                    );
                    if mv.notated.check == CheckStatus::Checkmate
                        && computed_check == CheckStatus::Check
                    {
                        for mv in board.legal_moves() {
                            eprintln!("Detected move:\n{mv:?}")
                        }
                    }
                    continue 'gameloop;
                }
                // TODO Add a separate test for these once I have a pool of moves and board states.
                /* TODO This doesn't work with the dataset because some moves are overspecified
                let computed_algebraic = board_copy
                    .move_to_algebraic(board_copy.detail_algebraic_move(mv.notated).unwrap());
                if computed_algebraic != mv.notated {
                    eprintln!(
                        "Disagree on move {} from board fen:\n{}\nin game {}\nchose {}\n",
                        mv.notated,
                        board_copy.to_fen(),
                        game.identifier,
                        computed_algebraic,
                    );
                    failure_count += 1;
                    continue 'gameloop;
                }
                */
                assert_eq!(board, BitboardRepresentation::from_fen(&board.to_fen()));
            }
        }
        let success_count = games_played - failure_count;
        println!(
            "{}/{} games successfully played ({:.1}%)",
            success_count,
            games_played,
            (success_count as f64) / (games_played as f64) * 100.,
        );
        if failure_count > 0 {
            panic!();
        }
    }
}
