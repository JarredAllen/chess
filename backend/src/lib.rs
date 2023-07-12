use bitboard::BitboardRepresentation;
use board::{AlgebraicNotationMove, Board, Color, GameOutcome};
use players::Player;

/// A backend which queries moves from the two players until the game is done
#[derive(Debug)]
pub struct Backend<White, Black> {
    /// The current state of the board
    gamestate: BitboardRepresentation,
    /// The white player
    white_player: White,
    /// The black player
    black_player: Black,
    /// The moves which have been played
    move_history: Vec<AlgebraicNotationMove>,
}

impl<White: Player, Black: Player> Backend<White, Black> {
    /// Create a new instance with the chess starting board
    pub fn new(mut white_player: White, mut black_player: Black) -> Self {
        const DEFAULT_FEN: &str = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
        white_player.position(DEFAULT_FEN, &[]);
        black_player.position(DEFAULT_FEN, &[]);
        Self {
            gamestate: BitboardRepresentation::INITIAL_STATE,
            white_player,
            black_player,
            move_history: Vec::new(),
        }
    }

    /// Query whoever's turn it is to make a move
    ///
    /// This updates the game state and also informs the other player that the move was made.
    pub fn play_half_move(&mut self) {
        let mv = match self.gamestate.side_to_move {
            Color::White => self.white_player.make_move(),
            Color::Black => self.black_player.make_move(),
        };
        self.move_history.push(
            self.gamestate.move_to_algebraic(
                self.gamestate
                    .detail_long_algebraic_move(mv)
                    .expect("Illegal move"),
            ),
        );
        self.gamestate
            .make_long_move(mv)
            .expect("Illegal move provided");
        match self.gamestate.side_to_move {
            Color::White => self.white_player.react_to_move(mv),
            Color::Black => self.black_player.react_to_move(mv),
        };
    }

    /// Play the game until it ends
    pub fn play_game(&mut self) {
        while self.game_state().game_outcome() == GameOutcome::InProgress {
            self.play_half_move();
        }
    }

    /// Get the state of the game right now
    pub fn game_state(&self) -> &impl Board {
        &self.gamestate
    }

    /// Get the PGN notation for this move
    pub fn to_pgn(&self) -> String {
        use core::fmt::Write;

        let mut pgn_buffer = String::new();
        for (move_count, moves) in self.move_history.chunks(2).enumerate() {
            let _ = pgn_buffer.write_fmt(format_args!("{}. {}", move_count + 1, moves[0]));
            if let Some(black) = moves.get(1) {
                let _ = pgn_buffer.write_fmt(format_args!(" {} ", black));
            }
        }
        if pgn_buffer.chars().nth_back(0) == Some(' ') {
            pgn_buffer.pop();
        }
        pgn_buffer.shrink_to_fit();
        pgn_buffer
    }
}

impl<White: Player + Default, Black: Player + Default> Default for Backend<White, Black> {
    fn default() -> Self {
        Self::new(White::default(), Black::default())
    }
}
