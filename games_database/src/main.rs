//! Generate a random sampling of positions on the board

use board::Board;
use games_database::lichess_jan_2013_database;
use rand::{rngs::SmallRng, Rng, SeedableRng};

fn main() {
    let mut positions = Vec::with_capacity(lichess_jan_2013_database().len() * 4);
    let mut rng = SmallRng::from_entropy();
    let mut seen_openings = std::collections::HashSet::new();
    for game in lichess_jan_2013_database() {
        // Skip if the game is too short, nothing interesting happened
        if game.moves.len() < 5 {
            continue;
        }
        // If we've already seen this opening before, weight against it
        if seen_openings.contains(&game.opening) {
            // 5% chance of keeping an already-seen opening
            if !rng.gen_ratio(1, 20) {
                continue;
            }
        } else {
            seen_openings.insert(game.opening);
        }
        // Add a first move, biased towards the end of the range
        let floor_idx = rng.gen_range(2..game.moves.len() - 1);
        let move_idx = rng.gen_range(floor_idx..game.moves.len());
        positions.push(
            bitboard::BitboardRepresentation::from_move_sequence(
                game.moves[..move_idx].iter().map(|mv| mv.notated),
            )
            .unwrap(),
        );
        // Add more positions from later in the game
        if move_idx < game.moves.len() - 1 {
            let move_idx = rng.gen_range(move_idx + 1..game.moves.len());
            positions.push(
                bitboard::BitboardRepresentation::from_move_sequence(
                    game.moves[..move_idx].iter().map(|mv| mv.notated),
                )
                .unwrap(),
            );
            if rng.gen_ratio(1, 2) && move_idx < game.moves.len() - 1 {
                let move_idx = rng.gen_range(move_idx + 1..game.moves.len());
                positions.push(
                    bitboard::BitboardRepresentation::from_move_sequence(
                        game.moves[..move_idx].iter().map(|mv| mv.notated),
                    )
                    .unwrap(),
                );
                if rng.gen_ratio(1, 2) && move_idx < game.moves.len() - 1 {
                    let move_idx = rng.gen_range(move_idx + 1..game.moves.len());
                    positions.push(
                        bitboard::BitboardRepresentation::from_move_sequence(
                            game.moves[..move_idx].iter().map(|mv| mv.notated),
                        )
                        .unwrap(),
                    );
                }
            }
        }
    }
    for position in positions {
        println!("{}", position.to_fen());
    }
}
