use board::AlgebraicNotationMove;

use interner::LockedInterner as Interner;

use core::str::FromStr;
use std::{io, sync::OnceLock};

/// An entry in the file
///
/// Contains the move, and may contain some bonus annotations
#[non_exhaustive]
pub struct MoveEntry {
    /// The move that was done
    pub notated: AlgebraicNotationMove,
}

/// The entry representing a game in a PGN file
#[non_exhaustive]
pub struct GameEntry {
    /// The moves that were made
    pub moves: Vec<MoveEntry>,
    /// A unique (I think) identifier for the games
    ///
    /// If no identifier was provided (I don't think possible), this is "XXXXXXXX".
    pub identifier: String,
    /// The opening, if an opening was provided by the database
    pub opening: Option<&'static str>,
    // Note:
    // If a string is expected to be repeated, we intern it to save memory.
    // Otherwise, we keep around an owned `String` value.
}

/// The games from Lichess in January 2013
///
/// Data was obtained from <https://database.lichess.org/>, and is licensed under the CC0 license.
const LICHESS_JAN_2013_DATABASE: &str =
    include_str!("../games/lichess_db_standard_rated_2013-01.pgn");

/// A string interner for chess game openings
static OPENING_INTERNER: Interner = Interner::new();

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

pub fn parse_pgn_file(reader: impl io::BufRead) -> io::Result<Vec<GameEntry>> {
    // Preallocate a large number to save on copying
    let mut games = Vec::with_capacity(1_048_576);
    let mut game_identifier = None;
    let mut opening = None;
    for line in reader.lines() {
        let line = line?;
        match line.chars().next() {
            Some('\n') | None => continue,
            Some('[') => {
                let inside = &line[1..line.len() - 2];
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

    #[test]
    fn test_lichess_2013_01_parsing() {
        // Just check that it doesn't panic
        lichess_jan_2013_database();
    }
}
