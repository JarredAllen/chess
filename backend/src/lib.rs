use bitboard::BitboardRepresentation;
use board::Board;
use players::Player;

pub struct Backend<White, Black> {
    gamestate: BitboardRepresentation,
    white_player: White,
    black_player: Black,
}

impl<White: Player, Black: Player> Backend<White, Black> {
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

    pub fn play_game(&mut self) {
        loop {
            let white_move = self.white_player.make_move();
            self.gamestate
                .make_long_move(white_move)
                .expect("Illegal move");
            self.black_player.react_to_move(white_move);
            let black_move = self.black_player.make_move();
            self.gamestate
                .make_long_move(black_move)
                .expect("Illegal move");
            self.white_player.react_to_move(black_move);
        }
    }

    pub fn game_state(&self) -> &impl Board {
        &self.gamestate
    }
}

impl<White: Player, Black: Player> Default for Backend<White, Black> {
    fn default() -> Self {
        Self::new()
    }
}
