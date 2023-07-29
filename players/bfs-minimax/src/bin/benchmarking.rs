//! Benchmarking for this player

use std::{
    hint::black_box,
    time::{Duration, Instant},
};

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
    let mut player = BfsMinimaxPlayer::with_depth(depth);
    // Chosen randomly, but fixed for benchmark consistency
    let mut rng = SmallRng::seed_from_u64(2965354380665276332);
    // TODO Measure CPU usage instead of wall time for extra consistency
    let start_time = Instant::now();
    while start_time.elapsed() < run_duration {
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
    position_exploring_benchmark(2, Duration::from_millis(200));
    // Evaluate a real run
    let result = position_exploring_benchmark(3, Duration::from_secs(20));
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
