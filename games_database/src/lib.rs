use board::AlgebraicNotationMove;

use interner::LockedInterner as Interner;

use core::str::FromStr;
use std::{io, sync::OnceLock};

/// An entry in the file
///
/// Contains the move, and may contain some bonus annotations
#[non_exhaustive]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct MoveEntry {
    /// The move that was done
    pub notated: AlgebraicNotationMove,
}

/// The possible game variants that it might be
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum GameVariant {
    /// A normal game of chess
    Traditional,
    /// Chess960 was played, with the initial board at the given FEN string
    Chess960 { initial_fen: &'static str },
}

/// The entry representing a game in a PGN file
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GameEntry {
    /// The moves that were made
    pub moves: Vec<MoveEntry>,
    /// A unique (I think) identifier for the games
    ///
    /// If no identifier was provided (I don't think possible), this is "XXXXXXXX".
    pub identifier: String,
    /// The opening, if an opening was provided by the database
    pub opening: Option<&'static str>,
    pub variant: GameVariant,
    // Note:
    // If a string is expected to be repeated, we intern it to save memory.
    // Otherwise, we keep around an owned `String` value.
}

/// The games from Lichess in January 2013 in Chess960 variant
///
/// Data was obtained from <https://database.lichess.org/>, and is licensed under the CC0 license.
const LICHESS_CHESS960_JAN_2013_DATABASE: &str =
    include_str!("../games/lichess_db_chess960_rated_2013-01.pgn");

/// The games from Lichess in January 2013
///
/// Data was obtained from <https://database.lichess.org/>, and is licensed under the CC0 license.
const LICHESS_JAN_2013_DATABASE: &str =
    include_str!("../games/lichess_db_standard_rated_2013-01.pgn");

/// A random selection of positions from [`LICHESS_JAN_2013_DATABASE`]
///
/// Data was obtained from <https://database.lichess.org/>, and is licensed under the CC0 license.
const LICHESS_JAN_2013_POSITIONS: &str =
    include_str!("../positions/lichess_jan_2013_positions.txt");

/// A string interner for FEN strings
///
/// There may be a lot of them, but they'll come from Chess960, which only generates 960 different
/// openings.
static FEN_INTERNER: Interner = Interner::new();

/// A string interner for chess game openings
static OPENING_INTERNER: Interner = Interner::new();

/// Output the data from the Lichess dataset for ranked games in January 2013
///
/// Note: Reading this file is slow, so this function performs the read once and saves the result.
///
/// Data was obtained from <https://database.lichess.org/>, and is licensed under the CC0 license.
pub fn lichess_chess960_jan_2013_database() -> &'static [GameEntry] {
    static RESULT: OnceLock<&'static [GameEntry]> = OnceLock::new();
    RESULT.get_or_init(|| {
        let reader = LICHESS_CHESS960_JAN_2013_DATABASE.as_bytes();
        Box::leak(
            parse_pgn_file(reader)
                .expect("Failed to parse file contents as games")
                .into_boxed_slice(),
        )
    })
}

/// Output the data from the Lichess dataset for ranked games in January 2013
///
/// Note: Reading this file is slow, so this function performs the read once and saves the result.
///
/// Data was obtained from <https://database.lichess.org/>, and is licensed under the CC0 license.
pub fn lichess_jan_2013_database() -> &'static [GameEntry] {
    static RESULT: OnceLock<&'static [GameEntry]> = OnceLock::new();
    RESULT.get_or_init(|| {
        let reader = LICHESS_JAN_2013_DATABASE.as_bytes();
        Box::leak(
            parse_pgn_file(reader)
                .expect("Failed to parse file contents as games")
                .into_boxed_slice(),
        )
    })
}

/// Output board positions chosen randomly from [`lichess_jan_2013_database`]
///
/// The RNG is seeded such that the same value for `desired_count` should result in the same moves
/// output, for benchmarking purposes.
///
/// ```
/// use games_database::lichess_jan_2013_positions_sample;
/// assert_eq!(
///     lichess_jan_2013_positions_sample(250).count(),
///     250
/// );
/// ```
pub fn lichess_jan_2013_positions_sample(desired_count: u32) -> impl Iterator<Item = &'static str> {
    use rand::{rngs::SmallRng, Rng, SeedableRng};
    let mut remaining_positions = LICHESS_JAN_2013_POSITIONS.matches('\n').count() as u32 + 1;
    if remaining_positions < desired_count {
        panic!("Requested too many positions, we only have {remaining_positions}");
    }
    let mut remaining_choose = desired_count;
    // Seed chosen randomly, but consistent so benchmarks work the same
    let mut rng = SmallRng::seed_from_u64(2630238673012584694);
    // Pick at random, nudging probabilities so we'll get the exact requested number
    LICHESS_JAN_2013_POSITIONS.split('\n').filter(move |_| {
        if rng.gen_ratio(remaining_choose, remaining_positions) {
            remaining_positions -= 1;
            remaining_choose -= 1;
            true
        } else {
            remaining_positions -= 1;
            false
        }
    })
}

pub fn parse_pgn_file(reader: impl io::BufRead) -> io::Result<Vec<GameEntry>> {
    // Preallocate a large number to save on copying
    let mut games = Vec::with_capacity(1_048_576);
    let mut game_identifier = None;
    let mut opening = None;
    let mut fen = None;
    let mut variant = None;
    for line in reader.lines() {
        let line = line?;
        match line.chars().next() {
            Some('\n') | None => continue,
            Some('[') => {
                let inside = line[1..line.len() - 1].trim();
                let Some((key, value)) = inside.split_once(' ') else { continue; };
                let value = &value[1..value.len() - 1];
                match key {
                    "Site" => {
                        game_identifier =
                            Some(value.rfind('/').map_or_else(
                                || value.to_string(),
                                |idx| value[idx + 1..].to_string(),
                            ));
                    }
                    "Opening" => opening = Some(OPENING_INTERNER.intern(value)),
                    "FEN" => fen = Some(FEN_INTERNER.intern(value)),
                    "Variant" => {
                        variant = Some(match value {
                            "Chess960" => GameVariant::Chess960 {
                                initial_fen: fen.expect("Chess960 game missing starting FEN"),
                            },
                            _ => unimplemented!("Unkown variant of chess game: {value:?}"),
                        })
                    }
                    _ => {
                        // We don't care about this key
                        continue;
                    }
                }
            }
            Some('1') => {
                let mut words = line
                    .split(' ')
                    .filter(|word| word.chars().next().is_some_and(|c| !c.is_ascii_digit()))
                    .peekable();
                let mut moves = Vec::new();
                while let Some(mut word) = words.next() {
                    // TODO capture annotations if we want it
                    while word.ends_with('!') {
                        word = &word[..word.len() - 1];
                    }
                    while word.ends_with('?') {
                        word = &word[..word.len() - 1];
                    }
                    while word.ends_with('!') {
                        word = &word[..word.len() - 1];
                    }
                    let notated = AlgebraicNotationMove::from_str(word).unwrap_or_else(|e| {
                        panic!("Failed to parse move as algebraic notation '{word}':\n{e:?}")
                    });
                    if words.next_if_eq(&"{").is_some() {
                        // TODO capture PGN comments if we want to
                        while words.next().is_some_and(|word| word != "}") {}
                    }
                    moves.push(MoveEntry { notated });
                }
                games.push(GameEntry {
                    moves,
                    identifier: game_identifier
                        .take()
                        .unwrap_or_else(|| "XXXXXXXX".to_string()),
                    opening: opening.take(),
                    variant: variant.take().unwrap_or(GameVariant::Traditional),
                })
            }
            _ => panic!("Unexpected line: {line}"),
        }
    }
    games.shrink_to_fit();
    Ok(games)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: Thanks to the static [`OnceLock`] values, these tests will be basically instant if
    // some other tests elsewhere cause these databases to be generated.

    #[test]
    fn test_lichess_2013_01_parsing() {
        for game in lichess_jan_2013_database() {
            assert_eq!(game.variant, GameVariant::Traditional);
        }
    }

    #[test]
    fn test_lichess_chess960_2013_01_parsing() {
        // Just check that it doesn't panic
        for game in lichess_chess960_jan_2013_database() {
            assert!(
                matches!(game.variant, GameVariant::Chess960 { .. }),
                "{game:#?}"
            );
        }
    }
}
