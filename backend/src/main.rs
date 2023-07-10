use backend::Backend;
use monke::MonkePlayer;

fn main() {
    let mut backend: Backend<MonkePlayer, MonkePlayer> = Backend::new();
    backend.play_game();
}
