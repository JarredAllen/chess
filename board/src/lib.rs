use core::{fmt, str::FromStr};
use std::error;

/// The types of pieces there are
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PieceKind {
    Pawn,
    Rook,
    Knight,
    Bishop,
    Queen,
    King,
}

/// The colors a piece can have
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Color {
    Black,
    White,
}

/// A piece
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Piece {
    pub kind: PieceKind,
    pub color: Color,
}
impl Piece {
    pub const fn fen_letter(self) -> char {
        let letter = match self.kind {
            PieceKind::Pawn => 'p',
            PieceKind::Rook => 'r',
            PieceKind::Knight => 'n',
            PieceKind::Bishop => 'b',
            PieceKind::Queen => 'q',
            PieceKind::King => 'k',
        };
        match self.color {
            Color::White => letter.to_ascii_uppercase(),
            Color::Black => letter.to_ascii_lowercase(),
        }
    }
}

/// Functionality belonging to all boards that can be made
pub trait Board {
    fn from_fen(fen: &str) -> Self;

    fn to_fen(&self) -> String;
}

/// An index on the board
///
/// Stored in 0x88 method:
/// ```text
/// 0x12345678
///        +-+ Rank
///    +-+ File
///   +   + Must be zero, invalid position if 1
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BoardSquare(pub u8);
impl BoardSquare {
    /// An invalid square
    ///
    /// Please use this instead of making your own so it's obvious if a deliberately-invalid square
    /// appeared.
    pub const INVALID: Self = Self(0xee);

    /// Returns if this square is valid
    ///
    /// ```
    /// # use board::BoardSquare;
    /// assert!(!BoardSquare::INVALID.is_valid());
    /// ```
    pub const fn is_valid(self) -> bool {
        self.0 & 0x88 == 0
    }

    /// Converts self to a valid string, if legal
    pub const fn as_str_legal(self) -> Option<&'static str> {
        match self.0 {
            0 => Some("a1"),
            1 => Some("b1"),
            2 => Some("c1"),
            3 => Some("d1"),
            4 => Some("e1"),
            5 => Some("f1"),
            6 => Some("g1"),
            7 => Some("h1"),
            16 => Some("a2"),
            17 => Some("b2"),
            18 => Some("c2"),
            19 => Some("d2"),
            20 => Some("e2"),
            21 => Some("f2"),
            22 => Some("g2"),
            23 => Some("h2"),
            32 => Some("a3"),
            33 => Some("b3"),
            34 => Some("c3"),
            35 => Some("d3"),
            36 => Some("e3"),
            37 => Some("f3"),
            38 => Some("g3"),
            39 => Some("h3"),
            48 => Some("a4"),
            49 => Some("b4"),
            50 => Some("c4"),
            51 => Some("d4"),
            52 => Some("e4"),
            53 => Some("f4"),
            54 => Some("g4"),
            55 => Some("h4"),
            64 => Some("a5"),
            65 => Some("b5"),
            66 => Some("c5"),
            67 => Some("d5"),
            68 => Some("e5"),
            69 => Some("f5"),
            70 => Some("g5"),
            71 => Some("h5"),
            80 => Some("a6"),
            81 => Some("b6"),
            82 => Some("c6"),
            83 => Some("d6"),
            84 => Some("e6"),
            85 => Some("f6"),
            86 => Some("g6"),
            87 => Some("h6"),
            96 => Some("a7"),
            97 => Some("b7"),
            98 => Some("c7"),
            99 => Some("d7"),
            100 => Some("e7"),
            101 => Some("f7"),
            102 => Some("g7"),
            103 => Some("h7"),
            112 => Some("a8"),
            113 => Some("b8"),
            114 => Some("c8"),
            115 => Some("d8"),
            116 => Some("e8"),
            117 => Some("f8"),
            118 => Some("g8"),
            119 => Some("h8"),
            _ => None,
        }
    }

    /// Converts self to the string name for this position, or `"XX"` if illegal
    pub const fn as_str(self) -> &'static str {
        match self.as_str_legal() {
            Some(s) => s,
            None => "XX",
        }
    }

    /// Produce a board square from the rank and file, returning `None` if out of bounds
    pub const fn from_rank_file(rank: u8, file: u8) -> Option<Self> {
        if rank < 8 && file < 8 {
            Some(Self(rank << 4 | file))
        } else {
            None
        }
    }

    /// Returns the `(rank, file)` tuple if this position is valid
    pub const fn to_rank_file(self) -> Option<(u8, u8)> {
        if self.is_valid() {
            Some((self.0 >> 4, self.0 & 0x07))
        } else {
            None
        }
    }

    pub fn to_bitboard_occupancy(self) -> u64 {
        if self.is_valid() {
            1u64 << ((((self.0 & 0x70) >> 1) | (self.0 & 0x07)) as u64)
        } else {
            0
        }
    }
}
impl fmt::Debug for BoardSquare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BoardSquare")
            .field("repr", &format_args!("{:X}", self.0))
            .field("readable", &self.as_str_legal().unwrap_or("illegal"))
            .finish()
    }
}
impl fmt::Display for BoardSquare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
#[derive(Debug)]
pub struct BoardSquareFromStrErr;
impl fmt::Display for BoardSquareFromStrErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("board position string was invalid")
    }
}
impl error::Error for BoardSquareFromStrErr {}
impl FromStr for BoardSquare {
    type Err = BoardSquareFromStrErr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.as_bytes();
        if s.len() != 2 {
            return Err(BoardSquareFromStrErr);
        }
        let file = match s[0] {
            0x61 => 0,
            0x62 => 1,
            0x63 => 2,
            0x64 => 3,
            0x65 => 4,
            0x66 => 5,
            0x67 => 6,
            0x68 => 7,
            _ => return Err(BoardSquareFromStrErr),
        };
        let rank = match s[1] {
            0x31 => 0,
            0x32 => 1,
            0x33 => 2,
            0x34 => 3,
            0x35 => 4,
            0x36 => 5,
            0x37 => 6,
            0x38 => 7,
            _ => return Err(BoardSquareFromStrErr),
        };
        Ok(Self(rank << 4 | file))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_board_squares {
        ($(
            $name:ident($square:pat) $body:block
        )*) => {$(
            #[test]
            fn $name() {
                for repr in u8::MIN..=u8::MAX {
                    let $square = BoardSquare(repr);
                    $body
                }
            }
        )*};
    }

    macro_rules! test_valid_board_squares {
        ($(
            $name:ident($square:pat) $body:block
        )*) => {$(
            #[test]
            fn $name() {
                for repr in u8::MIN..=u8::MAX {
                    let square = BoardSquare(repr);
                    if square.is_valid() {
                        let $square = square;
                        $body
                    }
                }
            }
        )*};
    }

    test_board_squares!(
        test_board_square_str_knows_when_valid(square) { assert_eq!(square.is_valid(), square.as_str_legal().is_some()); }
    );

    test_valid_board_squares!(
        test_board_square_name_round_trip(square) { assert_eq!(square, BoardSquare::from_str(square.as_str()).unwrap()) }
    );
}
