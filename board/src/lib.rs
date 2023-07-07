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
impl PieceKind {
    /// All the kinds of pieces there are
    pub const KINDS: [PieceKind; 6] = [
        Self::Pawn,
        Self::Rook,
        Self::Knight,
        Self::Bishop,
        Self::Queen,
        Self::King,
    ];

    /// The capitalized version of the letter used for this piece in FEN
    pub const fn fen_letter(self) -> char {
        match self {
            Self::Pawn => 'P',
            Self::Rook => 'R',
            Self::Knight => 'N',
            Self::Bishop => 'B',
            Self::Queen => 'Q',
            Self::King => 'K',
        }
    }

    /// Whether a pawn can promote into this kind of piece
    pub const fn is_promotable(self) -> bool {
        match self {
            PieceKind::Pawn | PieceKind::King => false,
            PieceKind::Rook | PieceKind::Queen | PieceKind::Knight | PieceKind::Bishop => true,
        }
    }
}

/// The colors a piece can have
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Color {
    White,
    Black,
}
impl Color {
    pub const fn other(self) -> Self {
        match self {
            Color::White => Color::Black,
            Color::Black => Color::White,
        }
    }

    pub const fn is_black(self) -> bool {
        match self {
            Color::White => false,
            Color::Black => true,
        }
    }

    pub const fn is_white(self) -> bool {
        match self {
            Color::White => true,
            Color::Black => false,
        }
    }
}

/// A piece
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Piece {
    pub kind: PieceKind,
    pub color: Color,
}
impl Piece {
    pub const fn fen_letter(self) -> char {
        match self.color {
            Color::White => self.kind.fen_letter().to_ascii_uppercase(),
            Color::Black => self.kind.fen_letter().to_ascii_lowercase(),
        }
    }

    /// Returns an iterator of all pieces that exist
    pub fn all_pieces() -> impl Iterator<Item = Self> {
        [
            Self {
                kind: PieceKind::Pawn,
                color: Color::White,
            },
            Self {
                kind: PieceKind::Rook,
                color: Color::White,
            },
            Self {
                kind: PieceKind::Knight,
                color: Color::White,
            },
            Self {
                kind: PieceKind::Bishop,
                color: Color::White,
            },
            Self {
                kind: PieceKind::Queen,
                color: Color::White,
            },
            Self {
                kind: PieceKind::King,
                color: Color::White,
            },
            Self {
                kind: PieceKind::Pawn,
                color: Color::Black,
            },
            Self {
                kind: PieceKind::Rook,
                color: Color::Black,
            },
            Self {
                kind: PieceKind::Knight,
                color: Color::Black,
            },
            Self {
                kind: PieceKind::Bishop,
                color: Color::Black,
            },
            Self {
                kind: PieceKind::Queen,
                color: Color::Black,
            },
            Self {
                kind: PieceKind::King,
                color: Color::Black,
            },
        ]
        .into_iter()
    }
}

/// The possible outcomes of a game
pub enum GameOutcome {
    /// White checkmated black
    WhiteCheckmate,
    /// Black checkmated white
    BlackCheckmate,
    /// Draw because one player couldn't make any moves
    Draw,
}

/// Functionality belonging to all boards that can be made
pub trait Board: Sized {
    /// An error type that can be returned
    type Err: fmt::Debug;

    /// Parse a board from the given FEN
    fn from_fen(fen: &str) -> Self;

    /// Convert to a FEN string
    fn to_fen(&self) -> String;

    /// Get the state at the start of a chess game
    fn initial_state() -> Self;

    /// Make the given move, in place
    ///
    /// Returns `Some(())` if the move is legal, and `None` if it isn't.
    fn make_move(&mut self, mv: AlgebraicNotationMove) -> Result<(), Self::Err>;

    /// Make the board after the given sequence of moves
    fn from_move_sequence(
        moves: impl Iterator<Item = AlgebraicNotationMove>,
    ) -> Result<Self, Self::Err> {
        let mut state = Self::initial_state();
        for m in moves {
            state.make_move(m)?;
        }
        Ok(state)
    }

    /// Returns if the side to move is currently in check or checkmate
    fn check_status(&self) -> CheckStatus;
}

#[derive(Debug)]
pub struct AlgebraicNotationMoveParseError;

/// The data parsed out from a move in algebraic notation
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct AlgebraicNotationMove {
    /// What move happened on the board
    pub move_type: AlgebraicNotationMoveType,
    /// Whether the move leaves the opponent in check(mate)
    pub check: CheckStatus,
}
impl fmt::Display for AlgebraicNotationMove {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.move_type, self.check)
    }
}
impl FromStr for AlgebraicNotationMove {
    type Err = AlgebraicNotationMoveParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (check, s) = match s.chars().nth_back(0) {
            Some('+') => (CheckStatus::Check, &s[..s.len() - 1]),
            Some('#') => (CheckStatus::Checkmate, &s[..s.len() - 1]),
            _ => (CheckStatus::None, s),
        };
        Ok(Self {
            move_type: s.parse()?,
            check,
        })
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum AlgebraicNotationMoveType {
    /// A move which isn't a castle (because those are notated entirely unrelatedly)
    Normal(AlgebraicNotationNormalMove),
    CastleKingside,
    CastleQueenside,
}
impl fmt::Display for AlgebraicNotationMoveType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Normal(mv) => mv.fmt(f),
            Self::CastleKingside => f.write_str("O-O"),
            Self::CastleQueenside => f.write_str("O-O-O"),
        }
    }
}
impl FromStr for AlgebraicNotationMoveType {
    type Err = AlgebraicNotationMoveParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "O-O" | "0-0" => Self::CastleKingside,
            "O-O-O" | "0-0-0" => Self::CastleQueenside,
            _ => Self::Normal(s.parse()?),
        })
    }
}
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CheckStatus {
    None,
    Check,
    Checkmate,
}
/// Returns the status as appended to a move in algebraic notation
impl fmt::Display for CheckStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::None => "",
            Self::Check => "+",
            Self::Checkmate => "#",
        })
    }
}

/// All the data from a move that isn't a castle
///
/// This doesn't include the check status after the move, because that is shared with castling in
/// the [`AlgebraicNotationMove`] struct.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct AlgebraicNotationNormalMove {
    pub kind: PieceKind,
    pub from_file: Option<char>,
    pub from_rank: Option<u8>,
    pub capture: bool,
    pub to_square: BoardSquare,
    pub promotion: Option<PieceKind>,
}
impl fmt::Display for AlgebraicNotationNormalMove {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let piece = if self.kind == PieceKind::Pawn {
            String::new()
        } else {
            self.kind.fen_letter().to_string()
        };
        let from_file = self.from_file.map_or_else(String::new, |c| c.to_string());
        let from_rank = self.from_rank.map_or_else(String::new, |r| r.to_string());
        let capture = if self.capture { "x" } else { "" };
        let to_square = self.to_square.as_str();
        let promotion = self
            .promotion
            .map_or_else(String::new, |p| p.fen_letter().to_string());
        write!(
            f,
            "{}{}{}{}{}{}",
            piece, from_file, from_rank, capture, to_square, promotion
        )
    }
}
impl FromStr for AlgebraicNotationNormalMove {
    type Err = AlgebraicNotationMoveParseError;

    fn from_str(mut s: &str) -> Result<Self, Self::Err> {
        let kind = match s.chars().next() {
            Some('R') => {
                s = &s[1..];
                PieceKind::Rook
            }
            Some('N') => {
                s = &s[1..];
                PieceKind::Knight
            }
            Some('B') => {
                s = &s[1..];
                PieceKind::Bishop
            }
            Some('Q') => {
                s = &s[1..];
                PieceKind::Queen
            }
            Some('K') => {
                s = &s[1..];
                PieceKind::King
            }
            _ => PieceKind::Pawn,
        };
        let promotion = match (s.chars().nth_back(0), s.chars().nth_back(1)) {
            (Some('R'), Some('=')) => {
                s = &s[..s.len() - 2];
                Some(PieceKind::Rook)
            }
            (Some('N'), Some('=')) => {
                s = &s[..s.len() - 2];
                Some(PieceKind::Knight)
            }
            (Some('B'), Some('=')) => {
                s = &s[..s.len() - 2];
                Some(PieceKind::Bishop)
            }
            (Some('Q'), Some('=')) => {
                s = &s[..s.len() - 2];
                Some(PieceKind::Queen)
            }
            _ => None,
        };
        let to_square = BoardSquare::from_str(&s[s.len() - 2..])
            .map_err(|_| AlgebraicNotationMoveParseError)?;
        s = &s[..s.len() - 2];
        let from_file = match s.chars().next() {
            Some(c @ ('a'..='h')) => {
                s = &s[1..];
                Some(c)
            }
            _ => None,
        };
        let from_rank = s.chars().next().and_then(|c| {
            if let Some(rank) = c.to_digit(10) {
                if 0 < rank && rank <= 8 {
                    s = &s[1..];
                    return Some(rank as u8);
                }
            }
            None
        });
        let capture = if s.starts_with('x') {
            s = &s[1..];
            true
        } else {
            false
        };
        debug_assert!(s.is_empty(), "{}", s);
        Ok(Self {
            kind,
            from_file,
            from_rank,
            capture,
            to_square,
            promotion,
        })
    }
}

/// An index on the board
///
/// Stored in 0x88 method:
/// ```text
/// 0b12345678
///        +-+ Rank
///    +-+ File
///   +   + Must be zero, invalid position if 1
/// ```
///
/// Each square is represented in one byte, and this format makes it easy to do operations and
/// check if the resulting square is valid and on the board.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BoardSquare(pub u8);
impl BoardSquare {
    /// An invalid square
    ///
    /// Please use this instead of making your own so it's obvious if a deliberately-invalid square
    /// appeared.
    pub const INVALID: Self = Self(0xee);

    pub const A1: Self = Self(0x00);
    pub const B1: Self = Self(0x01);
    pub const C1: Self = Self(0x02);
    pub const D1: Self = Self(0x03);
    pub const E1: Self = Self(0x04);
    pub const F1: Self = Self(0x05);
    pub const G1: Self = Self(0x06);
    pub const H1: Self = Self(0x07);
    pub const A2: Self = Self(0x10);
    pub const B2: Self = Self(0x11);
    pub const C2: Self = Self(0x12);
    pub const D2: Self = Self(0x13);
    pub const E2: Self = Self(0x14);
    pub const F2: Self = Self(0x15);
    pub const G2: Self = Self(0x16);
    pub const H2: Self = Self(0x17);
    pub const A3: Self = Self(0x20);
    pub const B3: Self = Self(0x21);
    pub const C3: Self = Self(0x22);
    pub const D3: Self = Self(0x23);
    pub const E3: Self = Self(0x24);
    pub const F3: Self = Self(0x25);
    pub const G3: Self = Self(0x26);
    pub const H3: Self = Self(0x27);
    pub const A4: Self = Self(0x30);
    pub const B4: Self = Self(0x31);
    pub const C4: Self = Self(0x32);
    pub const D4: Self = Self(0x33);
    pub const E4: Self = Self(0x34);
    pub const F4: Self = Self(0x35);
    pub const G4: Self = Self(0x36);
    pub const H4: Self = Self(0x37);
    pub const A5: Self = Self(0x40);
    pub const B5: Self = Self(0x41);
    pub const C5: Self = Self(0x42);
    pub const D5: Self = Self(0x43);
    pub const E5: Self = Self(0x44);
    pub const F5: Self = Self(0x45);
    pub const G5: Self = Self(0x46);
    pub const H5: Self = Self(0x47);
    pub const A6: Self = Self(0x50);
    pub const B6: Self = Self(0x51);
    pub const C6: Self = Self(0x52);
    pub const D6: Self = Self(0x53);
    pub const E6: Self = Self(0x54);
    pub const F6: Self = Self(0x55);
    pub const G6: Self = Self(0x56);
    pub const H6: Self = Self(0x57);
    pub const A7: Self = Self(0x60);
    pub const B7: Self = Self(0x61);
    pub const C7: Self = Self(0x62);
    pub const D7: Self = Self(0x63);
    pub const E7: Self = Self(0x64);
    pub const F7: Self = Self(0x65);
    pub const G7: Self = Self(0x66);
    pub const H7: Self = Self(0x67);
    pub const A8: Self = Self(0x70);
    pub const B8: Self = Self(0x71);
    pub const C8: Self = Self(0x72);
    pub const D8: Self = Self(0x73);
    pub const E8: Self = Self(0x74);
    pub const F8: Self = Self(0x75);
    pub const G8: Self = Self(0x76);
    pub const H8: Self = Self(0x77);

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

    /// Produce a board square from the rank and file, returning [`Self::INVALID`]` if the rank and
    /// file are not a valid square.
    pub const fn from_rank_file(rank: u8, file: u8) -> Self {
        if rank < 8 && file < 8 {
            Self(rank << 4 | file)
        } else {
            Self::INVALID
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

    /// Offset the given number of ranks and files.
    ///
    /// Positive rank moves from a towards h, while positive file moves towards bigger numbers.
    ///
    /// ```rust
    /// use board::BoardSquare;
    /// assert_eq!(BoardSquare::D2, BoardSquare::A1.offset(1, 3));
    /// assert_eq!(BoardSquare::A1, BoardSquare::D2.offset(-1, -3));
    /// assert_eq!(BoardSquare::F7, BoardSquare::F7.offset(0, 0));
    /// assert!(!BoardSquare::D1.offset(-1, 0).is_valid());
    /// assert!(!BoardSquare::D8.offset(1, 0).is_valid());
    /// assert!(!BoardSquare::A4.offset(0, -1).is_valid());
    /// assert!(!BoardSquare::H4.offset(0, 1).is_valid());
    /// ```
    pub const fn offset(self, rank: i8, file: i8) -> Self {
        BoardSquareOffset::from_rank_file(rank, file).offset(self)
    }

    /// An iterator over all valid squares on the board
    ///
    /// ```
    /// assert_eq!(board::BoardSquare::all_squares().count(), 64);
    /// ```
    pub fn all_squares() -> impl Iterator<Item = Self> {
        (0..64).map(|idx| {
            let file = idx & 0x07;
            let rank = (idx >> 3) & 0x07;
            Self(file | (rank << 4))
        })
    }

    /// Gets the offset to the given target
    ///
    /// If either input is invalid, then the resulting offset might make no sense.
    pub const fn offset_to(self, other: Self) -> BoardSquareOffset {
        let (Some((self_rank, self_file)), Some((other_rank, other_file))) = (self.to_rank_file(), other.to_rank_file()) else {
            return BoardSquareOffset::INVALID;
        };
        BoardSquareOffset::from_rank_file(
            self_rank as i8 - other_rank as i8,
            self_file as i8 - other_file as i8,
        )
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

/// An offset on a board
///
/// This struct stores any possible offset in both rank and file between any two squares, using
/// only one byte of space.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BoardSquareOffset(u8);
impl BoardSquareOffset {
    /// The offsets corresponding to all possible knight moves
    pub const KNIGHT_MOVES: [BoardSquareOffset; 8] = [
        Self::from_rank_file(2, 1),
        Self::from_rank_file(2, -1),
        Self::from_rank_file(-2, 1),
        Self::from_rank_file(-2, -1),
        Self::from_rank_file(1, 2),
        Self::from_rank_file(1, -2),
        Self::from_rank_file(-1, 2),
        Self::from_rank_file(-1, -2),
    ];

    /// The offsets corresponding to all possible king moves
    pub const KING_MOVES: [BoardSquareOffset; 8] = [
        Self::from_rank_file(1, 1),
        Self::from_rank_file(1, 0),
        Self::from_rank_file(1, -1),
        Self::from_rank_file(0, 1),
        Self::from_rank_file(0, -1),
        Self::from_rank_file(-1, 1),
        Self::from_rank_file(-1, 0),
        Self::from_rank_file(-1, -1),
    ];

    /// The moves a white pawn can make to attack
    pub const WHITE_PAWN_ATTACKS: [BoardSquareOffset; 2] =
        [Self::from_rank_file(1, 1), Self::from_rank_file(1, -1)];

    /// The moves a black pawn can make to attack
    pub const BLACK_PAWN_ATTACKS: [BoardSquareOffset; 2] =
        [Self::from_rank_file(-1, 1), Self::from_rank_file(-1, -1)];

    /// This is an invalid offset that, when applied to any [`BoardSquare`], invalidates it.
    pub const INVALID: Self = Self(0x88);

    /// Produce a new offset from the given rank and file amounts
    ///
    /// In debug mode, we assert that the rank and file are both on the interval [-7,7] (which are
    /// the only possible offsets). In release mode, we wrap modulo 16 and allow for -8, which
    /// invalidates any square.
    pub const fn from_rank_file(rank: i8, file: i8) -> Self {
        debug_assert!(-8 < rank && rank < 8);
        debug_assert!(-8 < file && file < 8);
        Self(((rank as u8) << 4) & 0xF0 | (file as u8) & 0x0F)
    }

    /// Offset the given board square
    ///
    /// If the square is already invalid, then the same square is returned unchanged.
    pub const fn offset(self, square: BoardSquare) -> BoardSquare {
        if square.is_valid() {
            BoardSquare(((self.0 & 0x77) + square.0) ^ (self.0 & 0x88))
        } else {
            square
        }
    }

    /// Gets the signed number of files associated with this offset
    pub const fn file(self) -> i8 {
        (self.0 as i8) << 4 >> 4
    }

    /// Gets the signed number of ranks associated with this offset
    pub const fn rank(self) -> i8 {
        (self.0 as i8) >> 4
    }

    /// Gets the taxicab distance metric for this offset
    pub const fn taxicab_distance(self) -> u8 {
        self.rank().unsigned_abs() + self.file().unsigned_abs()
    }

    /// Gets the Chebyshev distance for this offset
    ///
    /// This is the number of squares moved in one direction, for whichever direction is larger.
    pub const fn chebyshev_distance(self) -> u8 {
        let rank = self.rank().unsigned_abs();
        let file = self.file().unsigned_abs();
        if rank > file {
            rank
        } else {
            file
        }
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

    #[test]
    fn test_algebraic_round_trip() {
        #[track_caller]
        fn assert_round_trip(algebraic: &str) {
            let round_trip = AlgebraicNotationMove::from_str(algebraic)
                .expect("Couldn't parse input from string")
                .to_string();
            assert_eq!(algebraic, &round_trip);
        }
        assert_round_trip("e4");
        assert_round_trip("e4#");
        assert_round_trip("exd5");
        assert_round_trip("Qxd5");
        assert_round_trip("Qaxg8");
        assert_round_trip("Nb5xd4");
        assert_round_trip("O-O");
        assert_round_trip("O-O-O");
    }

    #[test]
    fn test_offset_rank_file() {
        for rank in -7..=7 {
            for file in -7..=7 {
                let offset = BoardSquareOffset::from_rank_file(rank, file);
                assert_eq!(offset.rank(), rank);
                assert_eq!(offset.file(), file);
            }
        }
    }
}
