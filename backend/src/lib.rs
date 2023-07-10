use bitboard::BitboardRepresentation;
use board::Board;
use players::Player;

pub struct Backend<P1, P2> {
    gamestate: BitboardRepresentation,
    player1: P1,
    player2: P2,
}

impl<P1: Player, P2: Player> Backend<P1, P2> {
    pub fn new() -> Self {
        const DEFAULT_FEN: &str = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
        let player1 = P1::position(DEFAULT_FEN, &[]);
        let player2 = P2::position(DEFAULT_FEN, &[]);
        Self {
            gamestate: BitboardRepresentation::INITIAL_STATE,
            player1,
            player2,
        }
    }

    pub fn play_game(&mut self) {
        loop {
            let p1move = self.player1.make_move();
            println!("P1 moved: {p1move}");
            self.gamestate.make_long_move(p1move).expect("Illegal move");
            self.player2.react_to_move(p1move);
            let p2move = self.player2.make_move();
            println!("P2 moved: {p2move}");
            self.gamestate.make_long_move(p2move).expect("Illegal move");
            self.player1.react_to_move(p2move);
        }
    }

    pub fn game_state(&self) -> &impl Board {
        &self.gamestate
    }
}

impl<P1: Player, P2: Player> Default for Backend<P1, P2> {
    fn default() -> Self {
        Self::new()
    }
}
