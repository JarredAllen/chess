use std::io::{self, Write};

use backend::Backend;
use bfs_minimax::BfsMinimaxPlayer;
use board::{Board, Color, GameOutcome};
use monke::MonkePlayer;
use terminal_ui::TerminalUIPlayer;

fn main() {
    let white = choose_player("white");
    let black = choose_player("black");
    let mut backend = Backend::new(white, black);
    backend.play_game();
    match backend.game_state().game_outcome() {
        GameOutcome::Draw => println!("Draw!"),
        GameOutcome::Won(Color::White) => println!("White wins!"),
        GameOutcome::Won(Color::Black) => println!("Black wins!"),
        GameOutcome::InProgress => unreachable!("Finished game is still in progress"),
    }
    println!("PGN:\n{}", backend.to_pgn());
}

fn choose_player(side: &str) -> Box<dyn players::Player> {
    let mut players = [
        (
            Box::new(MonkePlayer::new()) as Box<dyn players::Player>,
            "MonkePlayer",
        ),
        (Box::new(TerminalUIPlayer::new()), "TerminalUIPlayer"),
        (
            Box::new(BfsMinimaxPlayer::new(
                3,
                bfs_minimax::evaluate_board_material_score,
            )),
            "Minimax just material",
        ),
        (
            Box::new(BfsMinimaxPlayer::new(
                3,
                bfs_minimax::evaluate_board_material_score_and_squares_threatened,
            )),
            "Minimax threatening squares",
        ),
    ];
    loop {
        println!("Please pick among the following options for {side}:",);
        for (idx, (_, player)) in players.iter().enumerate() {
            println!("\t{player}: {idx}");
        }
        print!("Please input your choise (0-{}): ", players.len() - 1);
        let _ = io::stdout().flush();
        let mut response = String::new();
        let Ok(_len) = io::stdin().read_line(&mut response) else {
            continue;
        };
        let Ok(selection) = response.trim().parse::<usize>() else {
            println!(
                "\nCouldn't parse input {:?} as a number, try again\n",
                response.trim()
            );
            continue;
        };
        if selection >= players.len() {
            println!("\nSelection {selection} out of range, try again\n");
            continue;
        }
        players.swap(0, selection);
        let [player, ..] = players;
        break player.0;
    }
}
