use backend::Backend;
use monke::MonkePlayer;
use terminal_ui::TerminalUIPlayer;

fn main() {
    let mut backend: Backend<TerminalUIPlayer, MonkePlayer> = Backend::new();
    backend.play_game();
}
