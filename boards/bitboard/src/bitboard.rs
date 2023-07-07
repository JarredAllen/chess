use core::{
    fmt,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Not},
};

use board::{BoardSquare, BoardSquareOffset, Color, Piece, PieceKind};
use utils::debug_unreachable;

/// A bitboard (which is equivalent to a `u64`)
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Bitboard(pub u64);

macro_rules! bitboard_from_offsets {
    ($($offset:expr),* $(,)?) => {
        Bitboard(0 $(| 1 << {
            let offset = $offset;
            offset & 0x07 | (((offset >> 4) & 0x07) << 3)
        })*)
    };
}

impl Bitboard {
    /// Create an empty bitboard
    pub const fn empty() -> Self {
        Self(0)
    }

    /// Produce a bitboard from the given board square.
    ///
    /// If the board square is invalid, this return the empty bitboard.
    pub const fn from_board_square(square: BoardSquare) -> Self {
        if square.is_valid() {
            Self(1u64 << ((((square.0 & 0x70) >> 1) | (square.0 & 0x07)) as u64))
        } else {
            Self::empty()
        }
    }

    /// Gets a bitboard for the rank containing the given square
    pub const fn containing_rank(square: BoardSquare) -> Self {
        if square.is_valid() {
            let base = 1u64 << (((square.0 & 0x70) >> 1) as u64);
            Self(base * 0xFF)
        } else {
            Self::empty()
        }
    }

    pub const fn containing_diagonals(square: BoardSquare) -> Self {
        let Some((rank, file)) = square.to_rank_file() else { return Self::empty(); };
        let forward_diag = match (rank as i8) - (file as i8) {
            -7 => bitboard_from_offsets!(0x07),
            -6 => bitboard_from_offsets!(0x06, 0x17),
            -5 => bitboard_from_offsets!(0x05, 0x16, 0x27),
            -4 => bitboard_from_offsets!(0x04, 0x15, 0x26, 0x37),
            -3 => bitboard_from_offsets!(0x03, 0x14, 0x25, 0x36, 0x47),
            -2 => bitboard_from_offsets!(0x02, 0x13, 0x24, 0x35, 0x46, 0x57),
            -1 => bitboard_from_offsets!(0x01, 0x12, 0x23, 0x34, 0x45, 0x56, 0x67),
            0 => bitboard_from_offsets!(0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77),
            1 => bitboard_from_offsets!(0x10, 0x21, 0x32, 0x43, 0x54, 0x65, 0x76),
            2 => bitboard_from_offsets!(0x20, 0x31, 0x42, 0x53, 0x64, 0x75),
            3 => bitboard_from_offsets!(0x30, 0x41, 0x52, 0x63, 0x74),
            4 => bitboard_from_offsets!(0x40, 0x51, 0x62, 0x73),
            5 => bitboard_from_offsets!(0x50, 0x61, 0x72),
            6 => bitboard_from_offsets!(0x60, 0x71),
            7 => bitboard_from_offsets!(0x70),
            _ => debug_unreachable!(),
        };
        let backward_diag = match rank + file {
            0 => bitboard_from_offsets!(0x00),
            1 => bitboard_from_offsets!(0x10, 0x01),
            2 => bitboard_from_offsets!(0x20, 0x11, 0x02),
            3 => bitboard_from_offsets!(0x30, 0x21, 0x12, 0x03),
            4 => bitboard_from_offsets!(0x40, 0x31, 0x22, 0x13, 0x04),
            5 => bitboard_from_offsets!(0x50, 0x41, 0x32, 0x23, 0x14, 0x05),
            6 => bitboard_from_offsets!(0x60, 0x51, 0x42, 0x33, 0x24, 0x15, 0x06),
            7 => bitboard_from_offsets!(0x70, 0x61, 0x52, 0x43, 0x34, 0x25, 0x16, 0x07),
            8 => bitboard_from_offsets!(0x71, 0x62, 0x53, 0x44, 0x35, 0x26, 0x17),
            9 => bitboard_from_offsets!(0x72, 0x63, 0x54, 0x45, 0x36, 0x27),
            10 => bitboard_from_offsets!(0x73, 0x64, 0x55, 0x46, 0x37),
            11 => bitboard_from_offsets!(0x74, 0x65, 0x56, 0x47),
            12 => bitboard_from_offsets!(0x75, 0x66, 0x57),
            13 => bitboard_from_offsets!(0x76, 0x67),
            14 => bitboard_from_offsets!(0x77),
            _ => debug_unreachable!(),
        };
        Bitboard::union(forward_diag, backward_diag)
    }

    /// Gets a bitboard for the rank containing the given square
    pub const fn containing_file(square: BoardSquare) -> Self {
        if square.is_valid() {
            let base = 1u64 << ((square.0 & 0x07) as u64);
            Self(base * 0x01010101_01010101)
        } else {
            Self::empty()
        }
    }

    /// Get all the squares that are a knight move away
    pub const fn knight_moves(square: BoardSquare) -> Self {
        Self::from_board_square(square.offset(2, 1))
            .union(Self::from_board_square(square.offset(2, -1)))
            .union(Self::from_board_square(square.offset(-2, 1)))
            .union(Self::from_board_square(square.offset(-2, -1)))
            .union(Self::from_board_square(square.offset(1, 2)))
            .union(Self::from_board_square(square.offset(1, -2)))
            .union(Self::from_board_square(square.offset(-1, 2)))
            .union(Self::from_board_square(square.offset(-1, -2)))
    }

    /// Gets the bitboard representing the "middle" of a rook move.
    ///
    /// This does not contain the start or end squares.
    pub const fn rook_move_middle(start: BoardSquare, end: BoardSquare) -> Self {
        let Some((start_rank, start_file)) = start.to_rank_file() else { return Self::empty() };
        let Some((end_rank, end_file)) = end.to_rank_file() else { return Self::empty() };
        if start_rank == end_rank {
            let file_dir = if end_file > start_file { 1 } else { -1 };
            let mut board = Bitboard::empty();
            let mut file = start_file as i8 + file_dir;
            let rank = start_rank;
            while file as u8 != end_file {
                board = board.union(Bitboard::from_board_square(BoardSquare::from_rank_file(
                    rank, file as u8,
                )));
                file += file_dir;
            }
            board
        } else if start_file == end_file {
            let rank_dir = if end_rank > start_rank { 1 } else { -1 };
            let mut board = Bitboard::empty();
            let mut rank = start_rank as i8 + rank_dir;
            let file = start_file;
            while rank as u8 != end_rank {
                board = board.union(Bitboard::from_board_square(BoardSquare::from_rank_file(
                    rank as u8, file,
                )));
                rank += rank_dir;
            }
            board
        } else {
            debug_assert!(false, "Unreachable: Bitboard for illegal rook move");
            Bitboard::empty()
        }
    }

    /// Gets the bitboard representing the "middle" of a rook move.
    ///
    /// This does not contain the start or end squares.
    pub const fn bishop_move_middle(start: BoardSquare, end: BoardSquare) -> Self {
        let Some((start_rank, start_file)) = start.to_rank_file() else { return Self::empty() };
        let Some((end_rank, end_file)) = end.to_rank_file() else { return Self::empty() };
        debug_assert!(
            start_rank.abs_diff(end_rank) == start_file.abs_diff(end_file),
            "Unreachable: Bitboard for illegal bishop move"
        );
        let rank_dir = if end_rank > start_rank { 1 } else { -1 };
        let file_dir = if end_file > start_file { 1 } else { -1 };
        let mut rank = start_rank as i8 + rank_dir;
        let mut file = start_file as i8 + file_dir;
        let mut board = Bitboard::empty();
        while rank as u8 != end_rank && file as u8 != end_file {
            board = board.union(Bitboard::from_board_square(BoardSquare::from_rank_file(
                rank as u8, file as u8,
            )));
            rank += rank_dir;
            file += file_dir;
        }
        board
    }

    /// Returns all of the spaces threatened by a piece of the given kind on this bitboard, with
    /// the given squares blocked by pieces.
    ///
    /// For the purposes of this, we assume that the squares blocked are enemy pieces that we can
    /// capture, so those squares are threatened.
    pub fn squares_threatened(self, piece: Piece, blockers: Self) -> Self {
        match (piece.kind, piece.color) {
            (PieceKind::King, _) => self
                .squares_iter()
                .flat_map(|sq| {
                    BoardSquareOffset::KING_MOVES
                        .into_iter()
                        .map(move |offset| offset.offset(sq))
                })
                .filter(|sq| sq.is_valid())
                .fold(Self::empty(), |board, square| {
                    board.union(Bitboard::from_board_square(square))
                }),
            (PieceKind::Knight, _) => self
                .squares_iter()
                .flat_map(|sq| {
                    BoardSquareOffset::KNIGHT_MOVES
                        .into_iter()
                        .map(move |offset| offset.offset(sq))
                })
                .filter(|sq| sq.is_valid())
                .fold(Self::empty(), |board, square| {
                    board.union(Bitboard::from_board_square(square))
                }),
            (PieceKind::Pawn, Color::White) => self
                .squares_iter()
                .flat_map(|sq| {
                    BoardSquareOffset::WHITE_PAWN_ATTACKS
                        .into_iter()
                        .map(move |offset| offset.offset(sq))
                })
                .filter(|sq| sq.is_valid())
                .fold(Self::empty(), |board, square| {
                    board.union(Bitboard::from_board_square(square))
                }),
            (PieceKind::Pawn, Color::Black) => self
                .squares_iter()
                .flat_map(|sq| {
                    BoardSquareOffset::BLACK_PAWN_ATTACKS
                        .into_iter()
                        .map(move |offset| offset.offset(sq))
                })
                .filter(|sq| sq.is_valid())
                .fold(Self::empty(), |board, square| {
                    board.union(Bitboard::from_board_square(square))
                }),
            (PieceKind::Bishop, _) => self
                .squares_iter()
                .map(|square| {
                    let mut newly_threatened = Bitboard::empty();
                    for offset in [
                        BoardSquareOffset::from_rank_file(1, 1),
                        BoardSquareOffset::from_rank_file(1, -1),
                        BoardSquareOffset::from_rank_file(-1, 1),
                        BoardSquareOffset::from_rank_file(-1, -1),
                    ] {
                        let mut new_square = offset.offset(square);
                        while new_square.is_valid() {
                            newly_threatened |= Bitboard::from(new_square);
                            if blockers.intersects(Bitboard::from(new_square)) {
                                break;
                            }
                            new_square = offset.offset(new_square);
                        }
                    }
                    newly_threatened
                })
                .fold(Self::empty(), Bitboard::union),
            (PieceKind::Rook, _) => self
                .squares_iter()
                .map(|square| {
                    let mut newly_threatened = Bitboard::empty();
                    for offset in [
                        BoardSquareOffset::from_rank_file(1, 0),
                        BoardSquareOffset::from_rank_file(-1, 0),
                        BoardSquareOffset::from_rank_file(0, 1),
                        BoardSquareOffset::from_rank_file(0, -1),
                    ] {
                        let mut new_square = offset.offset(square);
                        while new_square.is_valid() {
                            newly_threatened |= Bitboard::from(new_square);
                            if blockers.intersects(Bitboard::from(new_square)) {
                                break;
                            }
                            new_square = offset.offset(new_square);
                        }
                    }
                    newly_threatened
                })
                .fold(Self::empty(), Bitboard::union),
            // Break the queen down into a rook and a bishop
            (PieceKind::Queen, _) => self
                .squares_threatened(
                    Piece {
                        kind: PieceKind::Rook,
                        ..piece
                    },
                    blockers,
                )
                .union(self.squares_threatened(
                    Piece {
                        kind: PieceKind::Bishop,
                        ..piece
                    },
                    blockers,
                )),
        }
    }
}
/// Ways to query
impl Bitboard {
    /// Query if the bitboard is empty
    ///
    /// ```
    /// use bitboard::Bitboard;
    /// assert!(Bitboard::empty().is_empty());
    /// assert!(!Bitboard(0x01).is_empty());
    /// ```
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Returns true if `self & other` is not empty
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// Returns true if `self & other == other`
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// Produce an iterator of all selected board squares from a bitboard
    ///
    /// ```
    /// use board::BoardSquare;
    /// use bitboard::{Bitboard, BitboardRepresentation};
    /// assert_eq!(Bitboard::empty().squares_iter().count(), 0);
    /// assert_eq!(
    ///     BitboardRepresentation::INITIAL_STATE.white_rook.squares_iter().collect::<Vec<_>>(),
    ///     vec![BoardSquare::A1, BoardSquare::H1],
    /// );
    /// assert_eq!(
    ///     BitboardRepresentation::INITIAL_STATE.black_knight.squares_iter().collect::<Vec<_>>(),
    ///     vec![BoardSquare::B8, BoardSquare::G8],
    /// );
    /// assert_eq!(Bitboard(!0).squares_iter().count(), 64);
    /// ```
    pub fn squares_iter(self) -> impl Iterator<Item = BoardSquare> {
        (0..=63)
            .filter(move |&offset| self.0 & (1 << offset) != 0)
            .map(|offset| BoardSquare::from_rank_file((offset >> 3) & 0x07, offset & 0x07))
    }

    /// Returns the number of bits which are set
    pub fn num_set(self) -> u32 {
        self.0.count_ones()
    }
}

/// Bit-wise operations for combining things
impl Bitboard {
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    pub const fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    pub const fn negation(self) -> Self {
        Self(!self.0)
    }
}

impl BitOr<Bitboard> for Bitboard {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.union(rhs)
    }
}
impl BitOr<BoardSquare> for Bitboard {
    type Output = Self;

    fn bitor(self, rhs: BoardSquare) -> Self::Output {
        self.union(Self::from(rhs))
    }
}
impl<T> BitOrAssign<T> for Bitboard
where
    Bitboard: BitOr<T, Output = Bitboard>,
{
    fn bitor_assign(&mut self, rhs: T) {
        *self = *self | rhs
    }
}
impl BitAnd<Bitboard> for Bitboard {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.intersection(rhs)
    }
}
impl<T> BitAndAssign<T> for Bitboard
where
    Bitboard: BitAnd<T, Output = Bitboard>,
{
    fn bitand_assign(&mut self, rhs: T) {
        *self = *self & rhs
    }
}
impl Not for Bitboard {
    type Output = Self;
    fn not(self) -> Self::Output {
        self.negation()
    }
}

impl From<BoardSquare> for Bitboard {
    fn from(value: BoardSquare) -> Self {
        Self::from_board_square(value)
    }
}
impl fmt::Debug for Bitboard {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Bitboard")
            .field(&format_args!("{:X}", self.0))
            .finish()
    }
}
/// Display as a TUI version of a grid
///
/// ```
/// use bitboard::Bitboard;
/// use board::BoardSquare;
///
/// assert_eq!(
///     Bitboard::from(BoardSquare::A1).to_string(),
///     "        \n        \n        \n        \n        \n        \n        \nX       \n",
/// );
/// assert_eq!(
///     Bitboard::from(BoardSquare::A8).to_string(),
///     "X       \n        \n        \n        \n        \n        \n        \n        \n",
/// );
/// assert_eq!(
///     Bitboard::from(BoardSquare::H1).to_string(),
///     "        \n        \n        \n        \n        \n        \n        \n       X\n",
/// );
/// assert_eq!(
///     Bitboard::from(BoardSquare::H8).to_string(),
///     "       X\n        \n        \n        \n        \n        \n        \n        \n",
/// );
/// ```
impl fmt::Display for Bitboard {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;
        for rank in (0..=7).rev() {
            for file in 0..=7 {
                f.write_char(if self.0 & (1 << (rank * 8 + file)) == 0 {
                    ' '
                } else {
                    'X'
                })?;
            }
            f.write_char('\n')?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use quickcheck::{quickcheck, Arbitrary, Gen};

    impl Arbitrary for Bitboard {
        fn arbitrary(g: &mut Gen) -> Self {
            Self(u64::arbitrary(g))
        }
    }

    quickcheck! {
        fn test_negation_round_trip(bitboard: Bitboard) -> bool {
            bitboard == !!bitboard
        }

        fn test_num_set_and_position_iter_agree(bitboard: Bitboard) -> bool {
            bitboard.num_set() as usize == bitboard.squares_iter().count()
        }
    }

    #[test]
    fn check_squares_contained_in_ranks_files() {
        for square in BoardSquare::all_squares() {
            assert!(
                Bitboard::containing_rank(square).contains(Bitboard::from_board_square(square)),
                "{square} not contained in its row",
            );
            assert!(
                Bitboard::containing_file(square).contains(Bitboard::from_board_square(square)),
                "{square} not contained in its file",
            );
        }
    }

    #[test]
    fn check_squares_contained_in_diagonals() {
        for square in BoardSquare::all_squares() {
            assert!(
                Bitboard::containing_diagonals(square)
                    .contains(Bitboard::from_board_square(square)),
                "{square} not contained in its diagonal",
            );
        }
    }
}
