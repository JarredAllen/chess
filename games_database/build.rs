use std::{
    fs::{self, File},
    io::{self, BufRead, Write},
    path::Path,
};

fn main() {
    // Download database files and extract them
    for (file_url, file_path) in [(
        "https://database.lichess.org/standard/lichess_db_standard_rated_2013-01.pgn.zst",
        &Path::new("games/lichess_db_standard_rated_2013-01.pgn"),
    )] {
        if file_path
            .try_exists()
            .expect("Error querying if file exists")
        {
            continue;
        }
        if let Some(parent) = file_path.parent() {
            fs::create_dir_all(parent).expect("Error creating directory");
        }
        let file_download = ureq::get(file_url)
            .call()
            .expect("Error requesting file")
            .into_reader();
        let decompressed = io::BufReader::new(
            zstd::Decoder::new(file_download).expect("Error interpreting data as zstd compressed"),
        )
        .lines();
        let mut output_file = File::create(file_path).expect("Failed to open file");
        for line in decompressed {
            output_file
                .write_all(line.expect("Error reading input from internet").as_bytes())
                .expect("Error writing to file");
        }
    }
}
