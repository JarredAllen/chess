use core::{fmt, str::FromStr};

use board::{Board, BoardSquare, Color, Piece, PieceKind};

bitflags::bitflags! {
    /// Which castles are allowed (the king and rook haven't moved yet)
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct CastleOptions: u8 {
        const WhiteKingside = 0b0000_0001;
        const WhiteQueenside = 0b0000_0010;
        const BlackKingside = 0b0000_0100;
        const BlackQueenside = 0b0000_1000;
    }
}

/// Represent using a bunch of bitboards
#[derive(Clone, PartialEq, Eq)]
pub struct Bitboards {
    // piece placement
    white_pawns: u64,
    white_rook: u64,
    white_knight: u64,
    white_bishop: u64,
    white_queen: u64,
    white_king: BoardSquare,
    black_pawns: u64,
    black_rook: u64,
    black_knight: u64,
    black_bishop: u64,
    black_queen: u64,
    black_king: BoardSquare,

    // flags
    /// Whether en passant is allowed and, if so, where
    ///
    /// If no en passant is allowed, then this will be an invalid square
    en_passant_target: BoardSquare,
    side_to_move: Color,
    castles: CastleOptions,

    // clocks
    /// Number of half-moves since pawn was moved or piece was captured
    ///
    /// Draw by 50 move rule when this counter hits 100
    halfmove_clock: u8,
    /// The number of turns elapsed in the game
    turn_counter: u16,
}

impl fmt::Debug for Bitboards {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Bitboards")
            .field("white_pawns", &format_args!("0x{:016X}", self.white_pawns))
            .field("white_rook", &format_args!("0x{:016X}", self.white_rook))
            .field(
                "white_knight",
                &format_args!("0x{:016X}", self.white_knight),
            )
            .field(
                "white_bishop",
                &format_args!("0x{:016X}", self.white_bishop),
            )
            .field("white_queen", &format_args!("0x{:016X}", self.white_queen))
            .field("white_king", &self.white_king)
            .field("black_pawns", &format_args!("0x{:016X}", self.black_pawns))
            .field("black_rook", &format_args!("0x{:016X}", self.black_rook))
            .field(
                "black_knight",
                &format_args!("0x{:016X}", self.black_knight),
            )
            .field(
                "black_bishop",
                &format_args!("0x{:016X}", self.black_bishop),
            )
            .field("black_queen", &format_args!("0x{:016X}", self.black_queen))
            .field("black_king", &self.black_king)
            .field("en_passant_target", &self.en_passant_target)
            .field("side_to_move", &self.side_to_move)
            .field("castles", &self.castles)
            .field("halfmove_clock", &self.halfmove_clock)
            .field("turn_counter", &self.turn_counter)
            .finish()
    }
}

impl Bitboards {
    /// A board with no pieces on it and no moves made
    pub const EMPTY: Self = Self {
        white_pawns: 0,
        white_rook: 0,
        white_knight: 0,
        white_bishop: 0,
        white_queen: 0,
        white_king: BoardSquare::INVALID,
        black_pawns: 0,
        black_rook: 0,
        black_knight: 0,
        black_bishop: 0,
        black_queen: 0,
        black_king: BoardSquare::INVALID,
        en_passant_target: BoardSquare::INVALID,
        side_to_move: Color::White,
        castles: CastleOptions::empty(),
        halfmove_clock: 0,
        turn_counter: 0,
    };

    /// The initial board state
    pub const INITIAL_STATE: Self = Self {
        white_pawns: 0xFF00,
        white_rook: 0x81,
        white_knight: 0x42,
        white_bishop: 0x24,
        white_queen: 0x08,
        white_king: BoardSquare(0x04),
        black_pawns: 0x00FF0000_00000000,
        black_rook: 0x81000000_00000000,
        black_knight: 0x42000000_00000000,
        black_bishop: 0x24000000_00000000,
        black_queen: 0x08000000_00000000,
        black_king: BoardSquare(0x74),
        en_passant_target: BoardSquare::INVALID,
        side_to_move: Color::White,
        castles: CastleOptions::all(),
        halfmove_clock: 0,
        turn_counter: 1,
    };

    /// Returns a bitboard of all occupied squares
    pub fn bitboard_occupied(&self) -> u64 {
        let nonkings = self.white_pawns
            | self.white_rook
            | self.white_knight
            | self.white_bishop
            | self.white_queen
            | self.black_pawns
            | self.black_rook
            | self.black_knight
            | self.black_bishop
            | self.black_queen;
        nonkings | self.white_king.to_bitboard_occupancy() | self.black_king.to_bitboard_occupancy()
    }

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
        let query_bitboard = square.to_bitboard_occupancy();
        macro_rules! check {
            ($query:ident: $($field:ident => ($color:ident, $kind:ident),)*) => {$(if $query & self.$field != 0 {
                return Some(Piece { color: Color::$color, kind: PieceKind::$kind, })
            })*};
        }
        check!(query_bitboard:
            white_pawns => (White, Pawn),
            white_rook => (White, Rook),
            white_knight => (White, Knight),
            white_bishop => (White, Bishop),
            white_queen => (White, Queen),
            black_pawns => (Black, Pawn),
            black_rook => (Black, Rook),
            black_knight => (Black, Knight),
            black_bishop => (Black, Bishop),
            black_queen => (Black, Queen),
        );
        None
    }
}

impl Board for Bitboards {
    fn to_fen(&self) -> String {
        let pieces = {
            let bitboard_occupied = self.bitboard_occupied();
            let rows = (0..=7)
                .map(|row_idx| {
                    let row_idx = 7 - row_idx;
                    if bitboard_occupied & (0xFF << (row_idx * 8)) == 0 {
                        return "8".to_string();
                    }
                    let mut positions = String::with_capacity(8);
                    let mut file_idx = 0;
                    let mut last_piece_file_idx = -1;
                    while let Some(position) = BoardSquare::from_rank_file(row_idx, file_idx) {
                        if let Some(piece) = self.get(position) {
                            let squares_skipped = file_idx as i16 - last_piece_file_idx;
                            if squares_skipped > 1 {
                                positions.push(
                                    char::from_digit(squares_skipped as u32 - 1, 10).unwrap(),
                                );
                            }
                            positions.push(piece.fen_letter());
                            last_piece_file_idx = file_idx as i16;
                            file_idx += 1;
                        } else {
                            file_idx += 1;
                        }
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
        let castling = {
            let mut options = String::with_capacity(4);
            if self.castles.contains(CastleOptions::WhiteKingside) {
                options.push('K');
            }
            if self.castles.contains(CastleOptions::WhiteQueenside) {
                options.push('Q');
            }
            if self.castles.contains(CastleOptions::BlackKingside) {
                options.push('k');
            }
            if self.castles.contains(CastleOptions::BlackQueenside) {
                options.push('q');
            }
            if options.is_empty() {
                options.push('-');
            }
            options
        };
        let en_passant_target = self.en_passant_target.as_str_legal().unwrap_or("-");
        let halfmove_clock = self.halfmove_clock;
        let fullmove_coutner = self.turn_counter;
        format!("{pieces} {side_to_move} {castling} {en_passant_target} {halfmove_clock} {fullmove_coutner}")
    }

    fn from_fen(fen: &str) -> Self {
        let mut board = Self::EMPTY;
        let mut terms = fen.split(' ');
        {
            let pieces = terms.next().expect("Error parsing FEN");
            for (rank_idx, rank) in pieces.split('/').enumerate() {
                let rank_idx = 7 - rank_idx;
                eprintln!("{}: {}", rank_idx, rank);
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
                                BoardSquare::from_rank_file(rank_idx as u8, file as u8)
                                    .expect("Error parsing FEN");
                            file += 1;
                            continue;
                        }
                        'k' => {
                            board.black_king =
                                BoardSquare::from_rank_file(rank_idx as u8, file as u8)
                                    .expect("Error parsing FEN");
                            file += 1;
                            continue;
                        }
                        'P' => &mut board.white_pawns,
                        'R' => &mut board.white_rook,
                        'N' => &mut board.white_knight,
                        'B' => &mut board.white_bishop,
                        'Q' => &mut board.white_queen,
                        'p' => &mut board.black_pawns,
                        'r' => &mut board.black_rook,
                        'n' => &mut board.black_knight,
                        'b' => &mut board.black_bishop,
                        'q' => &mut board.black_queen,
                        _ => panic!("Error parsing FEN"),
                    } |= 1 << (rank_idx * 8 + file);
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
        {
            let mut castling = terms.next().expect("Error parsing FEN");
            if castling.get(0..1) == Some("K") {
                board.castles |= CastleOptions::WhiteKingside;
                castling = &castling[1..];
            }
            if castling.get(0..1) == Some("Q") {
                board.castles |= CastleOptions::WhiteQueenside;
                castling = &castling[1..];
            }
            if castling.get(0..1) == Some("k") {
                board.castles |= CastleOptions::BlackKingside;
                castling = &castling[1..];
            }
            if castling.get(0..1) == Some("q") {
                board.castles |= CastleOptions::BlackQueenside;
            }
        }
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
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Ensure we don't increase the size on accident
    #[test]
    fn test_bitboard_size() {
        assert_eq!(core::mem::size_of::<Bitboards>(), 11 * 8);
    }

    #[test]
    fn test_opening_position_fen_parsing() {
        assert_eq!(
            Bitboards::INITIAL_STATE,
            Bitboards::from_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1")
        );
    }

    #[test]
    fn test_opening_position_to_fen() {
        assert_eq!(
            Bitboards::INITIAL_STATE.to_fen(),
            "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
        );
    }
}
