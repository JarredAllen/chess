//! Benchmarking for this player

use std::{hint::black_box, time::Duration};

use bfs_minimax::BfsMinimaxPlayer;
use players::Player;
use rand::{rngs::SmallRng, seq::SliceRandom, SeedableRng};

/// A benchmark result
struct BenchmarkResult {
    /// The number of positions explored during the benchmark
    positions_explored: usize,
    /// The amount of time spent exploring positions
    duration: Duration,
}

/// Benchmark the given depth of exploration for the given amount of time
#[inline(never)]
fn position_exploring_benchmark(depth: usize, run_duration: Duration) -> BenchmarkResult {
    let positions = games_database::lichess_jan_2013_positions_sample(2048).collect::<Vec<_>>();
    let mut player = BfsMinimaxPlayer::new(
        depth,
        bfs_minimax::evaluate_board_material_score_and_squares_threatened,
    );
    // Chosen randomly, but fixed for benchmark consistency
    let mut rng = SmallRng::seed_from_u64(2965354380665276332);
    while player.searching_time < run_duration {
        // The board setup is not counted towards the searching time
        let board = positions.choose(&mut rng).unwrap();
        player.position(board, &[]);
        black_box(player.make_move());
    }
    BenchmarkResult {
        positions_explored: player.positions_explored,
        duration: player.searching_time,
    }
}

#[inline(never)]
fn main() {
    // Pre-warm the cache
    position_exploring_benchmark(3, Duration::from_millis(100));
    // Evaluate a real run
    let result = position_exploring_benchmark(4, Duration::from_secs(20));
    println!(
        "{} positions explored in {}ms",
        result.positions_explored,
        result.duration.as_millis(),
    );
    println!(
        "Positions per ms: {:.2}",
        (result.positions_explored as f32) / (result.duration.as_micros() as f32 / 1000.)
    );
}
