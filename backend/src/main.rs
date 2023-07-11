use backend::Backend;
use board::{Board, Color, GameOutcome};
use monke::MonkePlayer;
use terminal_ui::TerminalUIPlayer;

fn main() {
    let mut backend: Backend<TerminalUIPlayer, MonkePlayer> = Backend::new();
    backend.play_game();
    match backend.game_state().game_outcome() {
        GameOutcome::Draw => println!("Draw!"),
        GameOutcome::Won(Color::White) => println!("White wins!"),
        GameOutcome::Won(Color::Black) => println!("Black wins!"),
        GameOutcome::InProgress => unreachable!("Finished game is still in progress"),
    }
    println!("PGN:\n{}", backend.to_pgn());
}
