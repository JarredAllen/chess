use bitboard::BitboardRepresentation;
use board::{Board, Color, GameOutcome};
use players::Player;

/// A backend which queries moves from the two players until the game is done
pub struct Backend<White, Black> {
    /// The current state of the board
    gamestate: BitboardRepresentation,
    /// The white player
    white_player: White,
    /// The black player
    black_player: Black,
}

impl<White: Player, Black: Player> Backend<White, Black> {
    /// Create a new instance with the chess starting board
    pub fn new() -> Self {
        const DEFAULT_FEN: &str = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
        let player1 = White::position(DEFAULT_FEN, &[]);
        let player2 = Black::position(DEFAULT_FEN, &[]);
        Self {
            gamestate: BitboardRepresentation::INITIAL_STATE,
            white_player: player1,
            black_player: player2,
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
}

impl<White: Player, Black: Player> Default for Backend<White, Black> {
    fn default() -> Self {
        Self::new()
    }
}
