//! A player which makes purely random moves

use std::time::Duration;

use bitboard::{BitboardRepresentation, DetailedMove};
use board::{Board, BoardSquare, Color, LongAlgebraicNotationMove, PieceKind};
use utils::UnreachableExpect;

use rand::{rngs::SmallRng, Rng, SeedableRng};

/// A player which makes a minimax tree
///
/// No special tricks are done
#[derive(Debug)]
pub struct BfsMinimaxPlayer {
    /// The state of the board
    pub board: BitboardRepresentation,
    /// The depth of tree to explore
    pub depth: usize,
    /// How we decide what to do
    rng: SmallRng,
    /// How many positions we've explored (for benchmarking)
    pub positions_explored: usize,
    /// How long we've spent exploring positions (for benchmarking)
    ///
    /// TODO Measure CPU usage instead of wall time for extra consistency
    pub searching_time: Duration,
}

impl BfsMinimaxPlayer {
    /// Create a new player with the initial board state
    pub fn new() -> Self {
        Self::with_depth(3)
    }
    /// Create a new player with the initial board state, to explore to the given depth
    pub fn with_depth(depth: usize) -> Self {
        Self {
            board: BitboardRepresentation::INITIAL_STATE,
            depth,
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
        let (mv, _eval) = evaluate_position(
            &self.board,
            &mut self.rng,
            self.depth,
            PositionEvaluation::MIN,
            PositionEvaluation::MAX,
            &mut positions_explored,
        );
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

#[derive(Debug, Copy, Clone)]
pub enum PositionEvaluation {
    CheckmatedCounter(u16),
    // This may never be NaN
    Evaluation(f32),
    CheckmateCounter(u16),
    Draw,
}
impl PositionEvaluation {
    /// The worst possible evaluation
    pub const MIN: Self = Self::CheckmatedCounter(0);
    /// The best possible evaluation
    pub const MAX: Self = Self::CheckmateCounter(0);
}
impl PartialEq for PositionEvaluation {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for PositionEvaluation {}
impl PartialOrd for PositionEvaluation {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PositionEvaluation {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self, other) {
            // Counting down until we get checkmated is the worst position
            (Self::CheckmatedCounter(n), Self::CheckmatedCounter(m)) => n.cmp(m),
            (Self::CheckmatedCounter(_), _) => Ordering::Less,
            (_, Self::CheckmatedCounter(_)) => Ordering::Greater,
            // Next up is evaluation or Draw (equal to 0.0 evaluation)
            (Self::Evaluation(n), Self::Evaluation(m)) => {
                n.partial_cmp(m).expect_unreachable("NaN evaluation")
            }
            (Self::Evaluation(n), Self::Draw) => {
                n.partial_cmp(&0.0).expect_unreachable("NaN evaluation")
            }
            (Self::Draw, Self::Evaluation(m)) => {
                0.0.partial_cmp(m).expect_unreachable("NaN evaluation")
            }
            (Self::Draw, Self::Draw) => Ordering::Equal,
            // Above all else is counting down until we checkmate
            (Self::CheckmateCounter(n), Self::CheckmateCounter(m)) => n.cmp(m).reverse(),
            (Self::CheckmateCounter(_), _) => Ordering::Greater,
            (_, Self::CheckmateCounter(_)) => Ordering::Less,
        }
    }
}
impl From<PositionEvaluation> for f32 {
    fn from(value: PositionEvaluation) -> Self {
        match value {
            PositionEvaluation::CheckmatedCounter(_) => f32::MIN,
            PositionEvaluation::Evaluation(eval) => eval,
            PositionEvaluation::Draw => 0.0,
            PositionEvaluation::CheckmateCounter(_) => f32::MAX,
        }
    }
}
/// Unary negation also increments move counters by one
impl std::ops::Neg for PositionEvaluation {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            PositionEvaluation::CheckmatedCounter(n) => PositionEvaluation::CheckmateCounter(n + 1),
            PositionEvaluation::Evaluation(n) => PositionEvaluation::Evaluation(-n),
            PositionEvaluation::Draw => PositionEvaluation::Draw,
            PositionEvaluation::CheckmateCounter(n) => PositionEvaluation::CheckmatedCounter(n + 1),
        }
    }
}

/// Evaluate the given position and return our evaluation and the best move to make
fn evaluate_position(
    position: &BitboardRepresentation,
    rng: &mut impl Rng,
    depth: usize,
    mut alpha: PositionEvaluation,
    beta: PositionEvaluation,
    positions_explored: &mut usize,
) -> (DetailedMove, PositionEvaluation) {
    let mut best_move = None;
    let mut best_eval = None;
    let mut num_tied_moves = 0;
    for mv in position.legal_moves() {
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
                    let (_opp_mv, opp_eval) = evaluate_position(
                        &post_move,
                        rng,
                        depth - 1,
                        -beta,
                        -alpha,
                        positions_explored,
                    );
                    -opp_eval
                }
            }
            // The game is drawn here
            board::GameOutcome::Draw => PositionEvaluation::Draw,
            // This can only happen if this move puts the opponent in checkmate
            board::GameOutcome::Won(_) => PositionEvaluation::CheckmateCounter(1),
        };
        match best_eval.map(|best_eval| eval.cmp(&best_eval)) {
            Some(std::cmp::Ordering::Less) => {}
            Some(std::cmp::Ordering::Equal) => {
                num_tied_moves += 1;
                if rng.gen_bool(1. / (num_tied_moves as f64)) {
                    best_move = Some(mv);
                    best_eval = Some(eval);
                }
            }
            Some(std::cmp::Ordering::Greater) => {
                num_tied_moves = 1;
                best_move = Some(mv);
                best_eval = Some(eval);
            }
            None => {
                debug_assert!(best_move.is_none());
                num_tied_moves = 1;
                best_move = Some(mv);
                best_eval = Some(eval);
            }
        }
        if best_eval.is_some_and(|best_eval| best_eval > beta) {
            return (
                best_move.expect("No legal moves from position"),
                best_eval.expect_unreachable("No legal moves from position"),
            );
        }
        alpha = alpha.max(best_eval.expect_unreachable("No legal moves from position"));
    }
    (
        best_move.expect("No legal moves from position"),
        best_eval.expect_unreachable("No legal moves from position"),
    )
}

fn evaluate_board_no_lookahead(board: &BitboardRepresentation, color: Color) -> PositionEvaluation {
    let evaluation = BoardSquare::all_squares()
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
        .sum();
    PositionEvaluation::Evaluation(evaluation)
}
