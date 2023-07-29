//! A player which makes purely random moves

use std::time::Duration;

use bitboard::{BitboardRepresentation, DetailedMove};
use board::{Board, BoardSquare, Color, LongAlgebraicNotationMove, PieceKind};

use rand::{rngs::SmallRng, Rng, SeedableRng};

/// A player which makes a minimax tree
///
/// No special tricks are done
#[derive(Debug)]
pub struct BfsMinimaxPlayer {
    /// The state of the board
    board: BitboardRepresentation,
    /// How we decide what to do
    rng: SmallRng,
    positions_explored: usize,
    searching_time: Duration,
}

impl BfsMinimaxPlayer {
    /// Create a new player with the initial board state.
    pub fn new() -> Self {
        Self {
            board: BitboardRepresentation::INITIAL_STATE,
            rng: SmallRng::from_entropy(),
            positions_explored: 0,
            searching_time: Duration::ZERO,
        }
    }
}

impl players::Player for BfsMinimaxPlayer {
    fn position(&mut self, fen: &str, moves: &[LongAlgebraicNotationMove]) {
        let mut board = BitboardRepresentation::from_fen(fen);
        for mv in moves {
            board.make_long_move(*mv).expect("Failed to make move");
        }
        self.board = board;
    }

    fn react_to_move(&mut self, opponent_move: LongAlgebraicNotationMove) {
        self.board
            .make_long_move(opponent_move)
            .expect("Failed to make move");
    }

    fn make_move(&mut self) -> LongAlgebraicNotationMove {
        let start = std::time::Instant::now();
        let mut positions_explored = 0;
        let (mv, _eval) = evaluate_position(&self.board, &mut self.rng, 2, &mut positions_explored);
        let elapsed = start.elapsed();
        self.positions_explored += positions_explored;
        self.searching_time += elapsed;
        println!(
            "Evaluated {positions_explored} positions in {}ms (total {} in {}ms)",
            elapsed.as_millis(),
            self.positions_explored,
            self.searching_time.as_millis(),
        );
        // SAFETY: This move was produced to be legal
        unsafe { self.board.do_move(mv) };
        mv.into()
    }
}

impl Default for BfsMinimaxPlayer {
    fn default() -> Self {
        Self::new()
    }
}

/// Evaluate the given position and return our evaluation and the best move to make
fn evaluate_position(
    position: &BitboardRepresentation,
    rng: &mut impl Rng,
    depth: usize,
    positions_explored: &mut usize,
) -> (DetailedMove, f32) {
    let (mv, eval) = position
        .legal_moves()
        .fold((None, f32::NAN), |(best_move, best_eval), mv| {
            *positions_explored += 1;
            let mut post_move = position.clone();
            // SAFETY: This move has been chosen to be legal
            unsafe {
                post_move.do_move(mv);
            }
            let eval = match post_move.game_outcome() {
                board::GameOutcome::InProgress => {
                    if depth == 0 {
                        evaluate_board_no_lookahead(&post_move, position.side_to_move)
                    } else {
                        let (_opp_mv, opp_eval) =
                            evaluate_position(&post_move, rng, depth - 1, positions_explored);
                        -opp_eval
                    }
                }
                // The game is drawn here
                board::GameOutcome::Draw => 0.0,
                // This can only happen if this move puts the opponent in checkmate
                board::GameOutcome::Won(_) => f32::MAX,
            };
            match eval.partial_cmp(&best_eval) {
                Some(std::cmp::Ordering::Less) => (best_move, best_eval),
                Some(std::cmp::Ordering::Equal) => {
                    if rng.gen_bool(0.5) {
                        (best_move, best_eval)
                    } else {
                        (Some(mv), eval)
                    }
                }
                Some(std::cmp::Ordering::Greater) => (Some(mv), eval),
                None => {
                    debug_assert!(best_move.is_none());
                    (Some(mv), eval)
                }
            }
        });
    (mv.expect("No legal moves from position"), eval)
}

fn evaluate_board_no_lookahead(board: &BitboardRepresentation, color: Color) -> f32 {
    BoardSquare::all_squares()
        .map(|square| {
            let Some(piece) = board.get(square) else { return 0.0; };
            let piece_value = match piece.kind {
                PieceKind::Pawn => 1.0,
                PieceKind::Rook => 5.0,
                PieceKind::Knight => 3.0,
                PieceKind::Bishop => 3.2,
                PieceKind::Queen => 9.0,
                PieceKind::King => 0.0,
            };
            if piece.color == color {
                piece_value
            } else {
                -piece_value
            }
        })
        .sum()
}
