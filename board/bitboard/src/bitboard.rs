use core::{
    fmt,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Not},
};

use board::{BoardSquare, Color, Piece, PieceKind};
use utils::{debug_impossible, debug_unreachable};

/// A bitboard (which is equivalent to a `u64`)
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Bitboard(pub u64);

/// Convert the given `0x88` notation offsets into a bitboard
macro_rules! bitboard_from_0x88_offsets {
    ($($offset:expr),* $(,)?) => {
        Bitboard(0 $(| 1 << {
            let offset = $offset;
            offset & 0x07 | (((offset >> 4) & 0x07) << 3)
        })*)
    };
}

/// Boilerplate reduction for optimization
///
/// This macro takes a normal function from a board square to a bitboard and precomputes a fixed
/// array of all possible inputs and their answers, to optimize.
///
/// This also only calls the method for legal board squares, and returns an empty bitboard for an
/// invalid input.
macro_rules! method_via_boardsquare_array {
    ( $(
        $( #[$meta:meta] )*
        $vis:vis $(const)? fn $fun_name:ident($square:ident: BoardSquare) -> Self
            $eval:block
    )* ) => { $(
        $(#[$meta])*
        $vis const fn $fun_name(square: BoardSquare) -> Self {
            /// Cache containing the answers
            const VALUES: [Bitboard; 256] = {
                let mut values = [Bitboard::empty(); 256];
                let mut idx: usize = 0;
                while idx < 256 {
                    if idx & 0x88 == 0 {
                        let $square = BoardSquare(idx as u8);
                        let bitboard = $eval;
                        values[idx] = bitboard;
                    }
                    idx += 1;
                }
                values
            };
            VALUES[square.0 as usize]
        }
    )* };
}

impl Bitboard {
    /// Create an empty bitboard
    #[inline]
    pub const fn empty() -> Self {
        Self(0)
    }

    method_via_boardsquare_array! {
        /// Produce a bitboard from the given board square.
        ///
        /// If the board square is invalid, this return the empty bitboard.
        #[inline]
        pub const fn from_board_square(square: BoardSquare) -> Self {
            Bitboard(1u64 << ((((square.0 & 0x70) >> 1) | (square.0 & 0x07)) as u64))
        }

        /// Gets a bitboard for the rank containing the given square
        #[inline]
        pub const fn containing_rank(square: BoardSquare) -> Self {
            let base = 1u64 << (((square.0 & 0x70) >> 1) as u64);
            Self(base * 0xFF)
        }

        /// Gets the diagonals containing the given square
        #[inline]
        pub const fn containing_diagonals(square: BoardSquare) -> Self {
            let rank = (square.0 & 0x70) >> 4;
            let file = square.0 & 0x07;
            let forward_diag = match (rank as i8) - (file as i8) {
                -7 => bitboard_from_0x88_offsets!(0x07),
                -6 => bitboard_from_0x88_offsets!(0x06, 0x17),
                -5 => bitboard_from_0x88_offsets!(0x05, 0x16, 0x27),
                -4 => bitboard_from_0x88_offsets!(0x04, 0x15, 0x26, 0x37),
                -3 => bitboard_from_0x88_offsets!(0x03, 0x14, 0x25, 0x36, 0x47),
                -2 => bitboard_from_0x88_offsets!(0x02, 0x13, 0x24, 0x35, 0x46, 0x57),
                -1 => bitboard_from_0x88_offsets!(0x01, 0x12, 0x23, 0x34, 0x45, 0x56, 0x67),
                0 => bitboard_from_0x88_offsets!(0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77),
                1 => bitboard_from_0x88_offsets!(0x10, 0x21, 0x32, 0x43, 0x54, 0x65, 0x76),
                2 => bitboard_from_0x88_offsets!(0x20, 0x31, 0x42, 0x53, 0x64, 0x75),
                3 => bitboard_from_0x88_offsets!(0x30, 0x41, 0x52, 0x63, 0x74),
                4 => bitboard_from_0x88_offsets!(0x40, 0x51, 0x62, 0x73),
                5 => bitboard_from_0x88_offsets!(0x50, 0x61, 0x72),
                6 => bitboard_from_0x88_offsets!(0x60, 0x71),
                7 => bitboard_from_0x88_offsets!(0x70),
                _ => debug_unreachable!(),
            };
            let backward_diag = match rank + file {
                0 => bitboard_from_0x88_offsets!(0x00),
                1 => bitboard_from_0x88_offsets!(0x10, 0x01),
                2 => bitboard_from_0x88_offsets!(0x20, 0x11, 0x02),
                3 => bitboard_from_0x88_offsets!(0x30, 0x21, 0x12, 0x03),
                4 => bitboard_from_0x88_offsets!(0x40, 0x31, 0x22, 0x13, 0x04),
                5 => bitboard_from_0x88_offsets!(0x50, 0x41, 0x32, 0x23, 0x14, 0x05),
                6 => bitboard_from_0x88_offsets!(0x60, 0x51, 0x42, 0x33, 0x24, 0x15, 0x06),
                7 => bitboard_from_0x88_offsets!(0x70, 0x61, 0x52, 0x43, 0x34, 0x25, 0x16, 0x07),
                8 => bitboard_from_0x88_offsets!(0x71, 0x62, 0x53, 0x44, 0x35, 0x26, 0x17),
                9 => bitboard_from_0x88_offsets!(0x72, 0x63, 0x54, 0x45, 0x36, 0x27),
                10 => bitboard_from_0x88_offsets!(0x73, 0x64, 0x55, 0x46, 0x37),
                11 => bitboard_from_0x88_offsets!(0x74, 0x65, 0x56, 0x47),
                12 => bitboard_from_0x88_offsets!(0x75, 0x66, 0x57),
                13 => bitboard_from_0x88_offsets!(0x76, 0x67),
                14 => bitboard_from_0x88_offsets!(0x77),
                _ => debug_unreachable!(),
            };
            Bitboard::union(forward_diag, backward_diag)
        }

        /// Gets a bitboard for the rank containing the given square
        #[inline]
        pub const fn containing_file(square: BoardSquare) -> Self {
            let base = 1u64 << ((square.0 & 0x07) as u64);
            Self(base * 0x01010101_01010101)
        }

        /// Get all the squares that are a king move away
        ///
        /// This only includes normal king moves, not castling.
        #[inline]
        pub const fn king_moves(square: BoardSquare) -> Self {
            Bitboard::from_board_square(square.offset(1, 1))
                .union(Bitboard::from_board_square(square.offset(1, 0)))
                .union(Bitboard::from_board_square(square.offset(1, -1)))
                .union(Bitboard::from_board_square(square.offset(0, 1)))
                .union(Bitboard::from_board_square(square.offset(0, 0)))
                .union(Bitboard::from_board_square(square.offset(0, -1)))
                .union(Bitboard::from_board_square(square.offset(-1, 1)))
                .union(Bitboard::from_board_square(square.offset(-1, 0)))
                .union(Bitboard::from_board_square(square.offset(-1, -1)))
        }

        /// Get all the squares that are a king move away
        ///
        /// This includes castling
        #[inline]
        pub const fn king_moves_with_castling(square: BoardSquare) -> Self {
            Bitboard::from_board_square(square.offset(1, 1))
                .union(Bitboard::from_board_square(square.offset(1, 0)))
                .union(Bitboard::from_board_square(square.offset(1, -1)))
                .union(Bitboard::from_board_square(square.offset(0, 1)))
                .union(Bitboard::from_board_square(square.offset(0, 0)))
                .union(Bitboard::from_board_square(square.offset(0, -1)))
                .union(Bitboard::from_board_square(square.offset(-1, 1)))
                .union(Bitboard::from_board_square(square.offset(-1, 0)))
                .union(Bitboard::from_board_square(square.offset(-1, -1)))
                .union(Bitboard::from_board_square(square.offset(0, 2)))
                .union(Bitboard::from_board_square(square.offset(0, -2)))
        }

        /// Get all the squares that are a knight move away
        #[inline]
        pub const fn knight_moves(square: BoardSquare) -> Self {
            Bitboard::from_board_square(square.offset(2, 1))
                .union(Bitboard::from_board_square(square.offset(2, -1)))
                .union(Bitboard::from_board_square(square.offset(-2, 1)))
                .union(Bitboard::from_board_square(square.offset(-2, -1)))
                .union(Bitboard::from_board_square(square.offset(1, 2)))
                .union(Bitboard::from_board_square(square.offset(1, -2)))
                .union(Bitboard::from_board_square(square.offset(-1, 2)))
                .union(Bitboard::from_board_square(square.offset(-1, -2)))
        }

        /// Get the squares that a white pawn can threaten
        #[inline]
        pub const fn white_pawn_attacks(square: BoardSquare) -> Self {
            Bitboard::from_board_square(square.offset(1, 1))
                .union(Bitboard::from_board_square(square.offset(1, -1)))
        }

        /// Get the squares that a black pawn can threaten
        #[inline]
        pub const fn black_pawn_attacks(square: BoardSquare) -> Self {
            Bitboard::from_board_square(square.offset(-1, 1))
                .union(Bitboard::from_board_square(square.offset(-1, -1)))
        }

        /// Get all squares on which an enemy piece could block a rook's movement
        ///
        /// ```
        /// use bitboard::Bitboard;
        /// use board::BoardSquare;
        ///
        /// assert_eq!(
        ///     Bitboard::rook_possible_blockers(BoardSquare::A1),
        ///     Bitboard(0x00_01_01_01_01_01_01_7E),
        /// );
        /// assert_eq!(
        ///     Bitboard::rook_possible_blockers(BoardSquare::A8),
        ///     Bitboard(0x7E_01_01_01_01_01_01_00),
        /// );
        /// ```
        #[inline]
        pub const fn rook_possible_blockers(square: BoardSquare) -> Self {
            let source_rank = (square.0 & 0x70) >> 4;
            let source_file = square.0 & 0x07;
            let mut newly_threatened = Bitboard::empty();
            {
                let mut target_rank = 1;
                while target_rank < 7 {
                    if target_rank == source_rank {
                        target_rank += 1;
                        continue;
                    }
                    newly_threatened = newly_threatened.union(Bitboard::from_board_square(
                        BoardSquare::from_rank_file(target_rank, source_file),
                    ));
                    target_rank += 1;
                }
            }
            {
                let mut target_file = 1;
                while target_file < 7 {
                    if target_file == source_file {
                        target_file += 1;
                        continue;
                    }
                    newly_threatened = newly_threatened.union(Bitboard::from_board_square(
                        BoardSquare::from_rank_file(source_rank, target_file),
                    ));
                    target_file += 1;
                }
            }
            newly_threatened
        }

        /// Get all squares on which an enemy piece could block a bishop's movement
        #[inline]
        pub const fn bishop_possible_blockers(square: BoardSquare) -> Self {
            Bitboard::containing_diagonals(square)
                .intersection(Bitboard(0x007E7E7E_7E7E7E00))
                .intersection(Bitboard::from_board_square(square).negation())
        }
    }

    /// Gets the bitboard representing the "middle" of a rook move.
    ///
    /// This does not contain the start or end squares.
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn squares_threatened(self, piece: Piece, blockers: Self) -> Self {
        match (piece.kind, piece.color) {
            (PieceKind::King, _) => self
                .squares_iter()
                .map(Self::king_moves)
                .fold(Self::empty(), |board, new| board.union(new)),
            (PieceKind::Knight, _) => self
                .squares_iter()
                .map(Self::knight_moves)
                .fold(Self::empty(), |board, new| board.union(new)),
            (PieceKind::Pawn, Color::White) => self
                .squares_iter()
                .map(Self::white_pawn_attacks)
                .fold(Self::empty(), |board, new| board.union(new)),
            (PieceKind::Pawn, Color::Black) => self
                .squares_iter()
                .map(Self::black_pawn_attacks)
                .fold(Self::empty(), |board, new| board.union(new)),
            (PieceKind::Bishop, _) => self
                .squares_iter()
                .map(|square| BISHOP_MAGIC_TABLE.lookup_bishop(square, blockers))
                .fold(Self::empty(), Bitboard::union),
            (PieceKind::Rook, _) => self
                .squares_iter()
                .map(|square| ROOK_MAGIC_TABLE.lookup_rook(square, blockers))
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

    /// Query if the bitboard is empty
    ///
    /// ```
    /// use bitboard::Bitboard;
    /// assert!(Bitboard::empty().is_empty());
    /// assert!(!Bitboard(0x01).is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Returns true if `self & other` is not empty
    #[inline]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// Returns true if `self & other == other`
    #[inline]
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
    #[inline]
    pub fn squares_iter(self) -> impl Iterator<Item = BoardSquare> {
        (0..=63)
            .filter(move |&offset| self.0 & (1 << offset) != 0)
            .map(|offset| BoardSquare::from_rank_file((offset >> 3) & 0x07, offset & 0x07))
    }

    /// Returns the number of bits which are set
    #[inline]
    pub fn num_set(self) -> u32 {
        self.0.count_ones()
    }
}

/// Bit-wise operations for combining things
///
/// These are `const` equivalents to `&`, `|`, `!`
impl Bitboard {
    #[inline]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    #[inline]
    pub const fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    #[inline]
    pub const fn negation(self) -> Self {
        Self(!self.0)
    }
}

impl BitOr<Bitboard> for Bitboard {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        self.union(rhs)
    }
}
impl BitOr<BoardSquare> for Bitboard {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: BoardSquare) -> Self::Output {
        self.union(Self::from(rhs))
    }
}
impl<T> BitOrAssign<T> for Bitboard
where
    Bitboard: BitOr<T, Output = Bitboard>,
{
    #[inline]
    fn bitor_assign(&mut self, rhs: T) {
        *self = *self | rhs
    }
}
impl BitAnd<Bitboard> for Bitboard {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        self.intersection(rhs)
    }
}
impl<T> BitAndAssign<T> for Bitboard
where
    Bitboard: BitAnd<T, Output = Bitboard>,
{
    #[inline]
    fn bitand_assign(&mut self, rhs: T) {
        *self = *self & rhs
    }
}
impl Not for Bitboard {
    type Output = Self;
    #[inline]
    fn not(self) -> Self::Output {
        self.negation()
    }
}

impl From<BoardSquare> for Bitboard {
    #[inline]
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

/// Get the index of the bitboard for a rook on this square
///
/// For an invalid square, returns `127`, which is never a valid index.
pub const fn rook_magic_bitboard_index(square: BoardSquare) -> usize {
    /// The indices (and bogus placeholders for speed)
    const INDICES: [usize; 256] = [
        0, 1, 2, 3, 4, 5, 6, 7, // Rank 1
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        1, 0, 3, 2, 5, 4, 7, 6, // Rank 2
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        8, 9, 10, 11, 12, 13, 14, 15, // Rank 3
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        9, 8, 11, 10, 13, 12, 15, 14, // Rank 4
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        16, 17, 18, 19, 20, 21, 22, 23, // Rank 5
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        17, 16, 19, 18, 21, 20, 23, 22, // Rank 6
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        24, 25, 26, 27, 28, 29, 30, 31, // Rank 7
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        25, 24, 27, 26, 29, 28, 31, 30, // Rank 8
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
    ];
    INDICES[square.0 as usize]
}
/// The bishop magic table
const ROOK_MAGIC_TABLE: &MagicAttackTable<32> = {
    #[repr(align(8))]
    struct AlignedBytes<const N: usize>([u8; N]);
    const TABLE_NUM_BYTES: usize = include_bytes!("../rook_attacks.bin").len();
    /// The raw bytes read from disk
    const BYTES: &AlignedBytes<TABLE_NUM_BYTES> =
        &AlignedBytes(*include_bytes!("../rook_attacks.bin"));
    let num_table_entries = (TABLE_NUM_BYTES
        - 32 * std::mem::size_of::<MagicAttackTablePerBoardData>())
        / std::mem::size_of::<Bitboard>();
    unsafe {
        &*(std::ptr::slice_from_raw_parts(BYTES.0.as_ptr().cast::<()>(), num_table_entries)
            as *const MagicAttackTable<32>)
    }
};

/// Get the index of the bitboard for a bishop on this square
///
/// For an invalid square, returns `127`, which is never a valid index.
#[inline]
pub const fn bishop_magic_bitboard_index(square: BoardSquare) -> usize {
    /// The indices (and bogus placeholders for speed)
    const INDICES: [usize; 256] = [
        0, 2, 4, 4, 4, 4, 12, 14, // Rank 1
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        0, 2, 5, 5, 5, 5, 12, 14, // Rank 2
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        0, 2, 6, 6, 6, 6, 12, 14, // Rank 3
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        0, 2, 7, 7, 7, 7, 12, 14, // Rank 4
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        1, 3, 8, 8, 8, 8, 13, 15, // Rank 5
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        1, 3, 9, 9, 9, 9, 13, 15, // Rank 6
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        1, 3, 10, 10, 10, 10, 13, 15, // Rank 7
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        1, 3, 11, 11, 11, 11, 13, 15, // Rank 8
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
        127, 127, 127, 127, 127, 127, 127, 127, // Bogus
    ];
    INDICES[square.0 as usize]
}

/// The bishop magic table
const BISHOP_MAGIC_TABLE: &MagicAttackTable<16> = {
    #[repr(align(8))]
    struct AlignedBytes<const N: usize>([u8; N]);
    const TABLE_NUM_BYTES: usize = include_bytes!("../bishop_attacks.bin").len();
    /// The raw bytes read from disk
    const BYTES: &AlignedBytes<TABLE_NUM_BYTES> =
        &AlignedBytes(*include_bytes!("../bishop_attacks.bin"));
    let num_table_entries = (TABLE_NUM_BYTES
        - 16 * std::mem::size_of::<MagicAttackTablePerBoardData>())
        / std::mem::size_of::<Bitboard>();
    unsafe {
        &*(std::ptr::slice_from_raw_parts(BYTES.0.as_ptr().cast::<()>(), num_table_entries)
            as *const MagicAttackTable<16>)
    }
};

/// The data per board in a [`MagicAttackTable`]
#[derive(Copy, Clone)]
struct MagicAttackTablePerBoardData {
    /// The magic number by which to multiply
    magic_number: u64,
    /// The number of bits to shift after multiplying
    shift: usize,
    /// The index into the table at which to start indexing for this board
    table_offset_begin: usize,
}

/// A table we can use to quickly reference bishop or rook moves
struct MagicAttackTable<const N: usize> {
    /// Per-bitboard data with instructions on how to index the table
    per_board_data: [MagicAttackTablePerBoardData; N],
    /// The bitboards containing our magic attacks
    table: [Bitboard],
}
impl MagicAttackTable<16> {
    /// Look up the squares threatened by a bishop located here
    #[inline]
    const fn lookup_bishop(&self, source: BoardSquare, blockers: Bitboard) -> Bitboard {
        let mask = Bitboard::bishop_possible_blockers(source);
        let board_index = bishop_magic_bitboard_index(source);
        let board_data = self.per_board_data[board_index];
        let attack_index = (mask
            .intersection(blockers)
            .0
            .wrapping_mul(board_data.magic_number)
            >> board_data.shift) as usize
            + board_data.table_offset_begin;
        {
            let table_end = if board_index == 15 {
                self.table.len()
            } else {
                self.per_board_data[board_index + 1].table_offset_begin
            };
            debug_impossible!(attack_index >= table_end);
        }
        self.table[attack_index].intersection(Bitboard::containing_diagonals(source))
    }
}
impl MagicAttackTable<32> {
    /// Look up the squares threatened by a bishop located here
    #[inline]
    const fn lookup_rook(&self, source: BoardSquare, blockers: Bitboard) -> Bitboard {
        let mask = Bitboard::rook_possible_blockers(source);
        let board_index = rook_magic_bitboard_index(source);
        let board_data = self.per_board_data[board_index];
        let attack_index = (mask
            .intersection(blockers)
            .0
            .wrapping_mul(board_data.magic_number)
            >> board_data.shift) as usize
            + board_data.table_offset_begin;
        {
            let table_end = if board_index == 31 {
                self.table.len()
            } else {
                self.per_board_data[board_index + 1].table_offset_begin
            };
            debug_impossible!(attack_index >= table_end);
        }
        self.table[attack_index].intersection(
            Bitboard::containing_rank(source).union(Bitboard::containing_file(source)),
        )
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

    #[test]
    fn check_bishop_blockers_contained_in_diagonals() {
        for square in BoardSquare::all_squares() {
            let diagonals = Bitboard::containing_diagonals(square);
            let blockers = Bitboard::bishop_possible_blockers(square);
            assert!(diagonals.contains(blockers));
            let differences = diagonals.0.count_ones() - blockers.0.count_ones();
            let expected_difference = match square.to_rank_file().unwrap() {
                (0 | 7, 0 | 7) => 2,
                (_, 0 | 7) | (0 | 7, _) => 3,
                _ => 5,
            };
            assert_eq!(
                differences, expected_difference,
                "For {square} difference was {differences} (expected {expected_difference}), blockers {blockers:?}",
            );
        }
    }

    #[test]
    fn check_rook_blockers_contained_in_ranks_files() {
        for square in BoardSquare::all_squares() {
            let rank_file =
                Bitboard::containing_rank(square).union(Bitboard::containing_file(square));
            let blockers = Bitboard::rook_possible_blockers(square);
            assert!(rank_file.contains(blockers));
            let differences = rank_file.0.count_ones() - blockers.0.count_ones();
            let expected_difference = match square.to_rank_file().unwrap() {
                (0 | 7, 0 | 7) => 3,
                (_, 0 | 7) | (0 | 7, _) => 4,
                _ => 5,
            };
            assert_eq!(
                differences, expected_difference,
                "For {square} difference was {differences} (expected {expected_difference}), blockers {blockers:?}",
            );
        }
    }
}
