use crate::Bitboard;
use board::{BoardSquare, Color, LongAlgebraicNotationMove, Piece, PieceKind};

/// All the details of a move figured out
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DetailedMove {
    pub piece: Piece,
    pub source: BoardSquare,
    pub target: BoardSquare,
    pub is_castle: bool,
    pub is_en_passant: bool,
    pub is_capture: bool,
    pub promotion_into: Option<PieceKind>,
}
impl DetailedMove {
    /// Black is castling to their queen side
    pub const BLACK_QUEENSIDE_CASTLE: Self = Self {
        piece: Piece {
            kind: PieceKind::King,
            color: Color::Black,
        },
        source: BoardSquare::E8,
        target: BoardSquare::C8,
        is_castle: true,
        is_en_passant: false,
        is_capture: false,
        promotion_into: None,
    };
    /// Black is castling to their king side
    pub const BLACK_KINGSIDE_CASTLE: Self = Self {
        piece: Piece {
            kind: PieceKind::King,
            color: Color::Black,
        },
        source: BoardSquare::E8,
        target: BoardSquare::G8,
        is_castle: true,
        is_en_passant: false,
        is_capture: false,
        promotion_into: None,
    };
    /// White is castling to their queen side
    pub const WHITE_QUEENSIDE_CASTLE: Self = Self {
        piece: Piece {
            kind: PieceKind::King,
            color: Color::White,
        },
        source: BoardSquare::E1,
        target: BoardSquare::C1,
        is_castle: true,
        is_en_passant: false,
        is_capture: false,
        promotion_into: None,
    };
    /// White is castling to their king side
    pub const WHITE_KINGSIDE_CASTLE: Self = Self {
        piece: Piece {
            kind: PieceKind::King,
            color: Color::White,
        },
        source: BoardSquare::E1,
        target: BoardSquare::G1,
        is_castle: true,
        is_en_passant: false,
        is_capture: false,
        promotion_into: None,
    };

    /// Check the legality of this move
    ///
    /// The given move is legal if all of the following criteria are met:
    ///  1. The piece in [`Self::piece`] is presently at the square [`Self::source`].
    ///  2. This function returns `Some((own, other))`.
    ///  3. `own` does not intersect the pieces owned by the moving player.
    ///  4. `other` does not intersect the pieces owned by the opposing player.
    ///  5. If [`Self::is_castle`] is set, then the rook is where it should be and the moving
    ///     player hasn't done any moves to interfere with the attempted castle.
    ///  6. If [`Self::is_en_passant`] is set, then there is a pawn that can be en passant-ed that
    ///     has just passed the target square.
    ///  7. If [`Self::is_capture`] is set, then there is an enemy piece on the target square (or
    ///     next to it, if [`Self::is_en_passant`] is set). Otherwise, there isn't.
    pub fn legality_check(self) -> Option<(Bitboard, Bitboard)> {
        let (source_rank, source_file) = self.source.to_rank_file()?;
        let (target_rank, target_file) = self.target.to_rank_file()?;
        if self.is_castle && self.piece.kind != PieceKind::King {
            return None;
        }
        if self.is_castle && self.is_capture {
            return None;
        }
        if self.is_en_passant && self.piece.kind != PieceKind::Pawn {
            return None;
        }
        if self.is_en_passant && !self.is_capture {
            return None;
        }
        if self.promotion_into.is_some() && self.piece.kind != PieceKind::Pawn {
            return None;
        }
        // No pieces can end where they started
        if self.source == self.target {
            return None;
        }
        match (self.piece.kind, self.piece.color) {
            (PieceKind::Pawn, Color::White) => {
                // Check promotion
                if self.promotion_into.is_some() && target_rank != 7
                    || self.promotion_into.is_none() && target_rank == 7
                {
                    return None;
                }
                if self
                    .promotion_into
                    .is_some_and(|piece| !piece.is_promotable())
                {
                    return None;
                }
                // Rest of the move
                if self.is_capture {
                    if self.is_en_passant && source_rank != 4 {
                        return None;
                    }
                    if target_rank.checked_sub(source_rank) == Some(1)
                        && target_file.abs_diff(source_file) == 1
                    {
                        let target = Bitboard::from(self.target);
                        Some((
                            target,
                            if self.is_en_passant {
                                target
                            } else {
                                Bitboard::empty()
                            },
                        ))
                    } else {
                        None
                    }
                } else {
                    if target_file != source_file {
                        return None;
                    }
                    if target_rank.checked_sub(source_rank) == Some(1) {
                        let board = Bitboard::from(self.target);
                        Some((board, board))
                    } else if source_rank == 1 && target_rank == 3 {
                        let board = Bitboard::from(self.target)
                            | Bitboard(Bitboard::from(self.target).0 >> 8);
                        Some((board, board))
                    } else {
                        None
                    }
                }
            }
            (PieceKind::Pawn, Color::Black) => {
                // Check promotion
                if self.promotion_into.is_some() && target_rank != 0
                    || self.promotion_into.is_none() && target_rank == 0
                {
                    return None;
                }
                if self
                    .promotion_into
                    .is_some_and(|piece| !piece.is_promotable())
                {
                    return None;
                }
                // Rest of the move
                if self.is_capture {
                    if self.is_en_passant && source_rank != 3 {
                        return None;
                    }
                    if source_rank.checked_sub(target_rank) == Some(1)
                        && target_file.abs_diff(source_file) == 1
                    {
                        let target = Bitboard::from(self.target);
                        Some((
                            target,
                            if self.is_en_passant {
                                target
                            } else {
                                Bitboard::empty()
                            },
                        ))
                    } else {
                        None
                    }
                } else {
                    if target_file != source_file {
                        return None;
                    }
                    if source_rank.checked_sub(target_rank) == Some(1) {
                        let board = Bitboard::from(self.target);
                        Some((board, board))
                    } else if source_rank == 6 && target_rank == 4 {
                        let board = Bitboard::from(self.target)
                            | Bitboard(Bitboard::from(self.target).0 << 8);
                        Some((board, board))
                    } else {
                        None
                    }
                }
            }
            (PieceKind::Rook, _) => {
                let board = if source_rank == target_rank || source_file == target_file {
                    Bitboard::rook_move_middle(self.source, self.target)
                } else {
                    return None;
                };
                let own_board = board | self.target;
                if self.is_capture {
                    Some((own_board, board))
                } else {
                    Some((own_board, own_board))
                }
            }
            (PieceKind::Bishop, _) => {
                if source_rank.abs_diff(target_rank) != source_file.abs_diff(target_file) {
                    return None;
                }
                let board = Bitboard::bishop_move_middle(self.source, self.target);
                let own_board = board | self.target;
                if self.is_capture {
                    Some((own_board, board))
                } else {
                    Some((own_board, own_board))
                }
            }
            (PieceKind::Queen, _) => {
                let board = if source_rank == target_rank || source_file == target_file {
                    Bitboard::rook_move_middle(self.source, self.target)
                } else if source_rank.abs_diff(target_rank) == source_file.abs_diff(target_file) {
                    Bitboard::bishop_move_middle(self.source, self.target)
                } else {
                    return None;
                };
                let own_board = board | self.target;
                if self.is_capture {
                    Some((own_board, board))
                } else {
                    Some((own_board, own_board))
                }
            }
            (PieceKind::Knight, _) => {
                if source_rank.abs_diff(target_rank) == 2 && source_file.abs_diff(target_file) == 1
                    || source_rank.abs_diff(target_rank) == 1
                        && source_file.abs_diff(target_file) == 2
                {
                    let target = Bitboard::from(self.target);
                    Some((
                        target,
                        if self.is_capture {
                            Bitboard::empty()
                        } else {
                            target
                        },
                    ))
                } else {
                    None
                }
            }
            (PieceKind::King, color) => {
                if source_rank.abs_diff(target_rank) <= 1 && source_file.abs_diff(target_file) <= 1
                {
                    let target = Bitboard::from(self.target);
                    Some((
                        target,
                        if self.is_capture {
                            Bitboard::empty()
                        } else {
                            target
                        },
                    ))
                } else if self.is_castle {
                    match color {
                        Color::White => {
                            if self.source != BoardSquare::E1 {
                                return None;
                            }
                            let required_vacant = match self.target {
                                BoardSquare::C1 => Bitboard(0x0E),
                                BoardSquare::G1 => Bitboard(0x60),
                                _ => return None,
                            };
                            Some((required_vacant, required_vacant))
                        }
                        Color::Black => {
                            if self.source != BoardSquare::E8 {
                                return None;
                            }
                            let required_vacant = match self.target {
                                BoardSquare::C8 => Bitboard(0x0E000000_00000000),
                                BoardSquare::G8 => Bitboard(0x60000000_00000000),
                                _ => return None,
                            };
                            Some((required_vacant, required_vacant))
                        }
                    }
                } else {
                    None
                }
            }
        }
    }

    /// Returns the square against which the opponent may respond with an en passant.
    ///
    /// If this move is not a double pawn move, then this is [`BoardSquare::INVALID`].
    pub(crate) fn en_passant_response(&self) -> BoardSquare {
        if self.piece.kind != PieceKind::Pawn || self.is_capture {
            return BoardSquare::INVALID;
        }
        let Some((source_rank, file)) = self.source.to_rank_file() else {
            return BoardSquare::INVALID;
        };
        let Some((target_rank, _)) = self.target.to_rank_file() else {
            return BoardSquare::INVALID;
        };
        if source_rank.abs_diff(target_rank) == 2 {
            BoardSquare::from_rank_file((source_rank + target_rank) / 2, file)
        } else {
            BoardSquare::INVALID
        }
    }
}
impl From<DetailedMove> for LongAlgebraicNotationMove {
    fn from(value: DetailedMove) -> Self {
        Self {
            source: value.source,
            target: value.target,
            promotion: value.promotion_into,
        }
    }
}
