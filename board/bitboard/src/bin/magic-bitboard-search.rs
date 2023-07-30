//! Search for the magic bitboards

use bitboard::Bitboard;
use board::BoardSquare;

use rand::{rngs::SmallRng, Rng, SeedableRng};
use std::{
    collections::HashSet,
    fs, io, iter,
    mem::MaybeUninit,
    path::Path,
    sync::{atomic::AtomicBool, Arc},
    thread,
    time::Duration,
};

/// Search for a magic number to differentiate between the given keys
///
/// The returned iterator will run until `stop` is true, so you should hang onto a reference to it.
fn magic_number_search(
    initial_key: u64,
    mut best_size: usize,
    keys: HashSet<Bitboard>,
    stop: Arc<AtomicBool>,
) -> impl Iterator<Item = (u64, usize)> {
    iter::successors(Some(initial_key), move |prev| {
        if stop.load(std::sync::atomic::Ordering::Relaxed) {
            return None;
        }
        // Quick xor-shift to ensure we hit all possible keys eventually
        let mut x = *prev;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        Some(x)
    })
    .filter_map(move |magic_number| {
        let mut mappings = HashSet::new();
        // Only try something better than the current best known
        let target_key_size = best_size - 1;
        let index_shift_amount = 64 - target_key_size;
        for key in &keys {
            if !mappings.insert(key.0.wrapping_mul(magic_number) >> index_shift_amount) {
                return None;
            }
        }
        best_size = target_key_size;
        Some((magic_number, target_key_size))
    })
}

/// For the mask, output all possible keys that can result
fn keys_from_mask(mask: Bitboard) -> impl Iterator<Item = Bitboard> {
    let num_bits = mask.0.count_ones() as usize;
    let bits = {
        let mut bits = Vec::with_capacity(num_bits);
        for idx in 0..64 {
            if (mask.0 >> idx) & 1 == 1 {
                bits.push(1 << idx);
            }
        }
        bits
    };
    (0..(1 << num_bits)).map(move |unshifted_key| {
        let mut key = 0;
        for (bit_number, bit_value) in bits.iter().enumerate() {
            if (unshifted_key >> bit_number) & 1 == 1 {
                key |= bit_value;
            }
        }
        Bitboard(key)
    })
}

/// Load the bitboards stored in the indicated file.
///
/// If the file does not exist, make a new file with a magic number of 1 and a size of 64 bits.
/// This size is guaranteed valid, but will be far too large to fit in a computer, so you should
/// search.
fn load_magics_from_file<const N: usize>(path: impl AsRef<Path>) -> io::Result<[(u64, usize); N]> {
    let path = path.as_ref();
    if path.exists() {
        let read = fs::read(path)?;
        let mut data = MaybeUninit::<[(u64, usize); N]>::uninit();
        if read.len() != std::mem::size_of_val(&data) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "File had wrong length of data",
            ));
        }
        // SAFETY:
        // Aliasing: We stop touching `slice` before we touch data again, so the borrows are
        // properly stacked.
        // Buffer length: The pointer and size belong to `data`, so the slice we make is valid.
        unsafe {
            let slice = std::slice::from_raw_parts_mut(
                data.as_mut_ptr().cast::<u8>(),
                std::mem::size_of_val(&data),
            );
            slice.copy_from_slice(&read);
            Ok(data.assume_init())
        }
    } else {
        let default = [(1, 64); N];
        save_magics_to_file(path, default)?;
        Ok(default)
    }
}

fn save_magics_to_file<const N: usize>(
    path: impl AsRef<Path>,
    magics: [(u64, usize); N],
) -> io::Result<()> {
    fs::write(path, unsafe {
        std::slice::from_raw_parts(magics.as_ptr().cast::<u8>(), std::mem::size_of_val(&magics))
    })
}

/// Generate better rook magic boards until `stop` becomes true
fn find_rook_magics(stop: Arc<AtomicBool>) {
    let bitboards: [HashSet<_>; 32] = {
        let mut bitboards = std::array::from_fn(|_| HashSet::new());
        for square in BoardSquare::all_squares() {
            bitboards[bitboard::bitboard::rook_magic_bitboard_index(square)]
                .extend(keys_from_mask(Bitboard::rook_possible_blockers(square)));
        }
        bitboards
    };
    let mut known_magics =
        load_magics_from_file::<32>("rook_magics.bin").expect("Failed to read rook magics");
    println!("Loaded current rook magics: {known_magics:?}");
    let (magics_sender, magics_receiver) =
        std::sync::mpsc::sync_channel::<((u64, usize), usize)>(32);
    let mut rng = SmallRng::from_entropy();
    let mut handles = Vec::new();
    for (board_number, keys) in bitboards.into_iter().enumerate() {
        let initial_key = rng.gen::<u64>();
        let stop = stop.clone();
        let magics_sender = magics_sender.clone();
        handles.push(thread::spawn(move || {
            for (magic_number, key_length) in magic_number_search(initial_key, known_magics[board_number].1, keys, stop) {
                println!("Found new magic number of rook bitboard {board_number}:\n0x{magic_number:X} (key length: {key_length})");
                magics_sender.send(((magic_number, key_length), board_number)).expect("Failed to send magic number");
            }
        }));
    }
    std::mem::drop(magics_sender);
    while let Ok((magic, board_number)) = magics_receiver.recv() {
        known_magics[board_number] = magic;
    }
    println!("Saving new rook magics: {known_magics:?}");
    save_magics_to_file("rook_magics.bin", known_magics).expect("Failed to save rook magics");
    println!(
        "New Rook magics size: {:.1}MB",
        known_magics
            .into_iter()
            .map(|(_, key_length)| 1 << (key_length + 3))
            .sum::<usize>() as f32
            / (1 << 20) as f32
    );
}

/// Generate better bishop magic boards until `stop` becomes true
fn find_bishop_magics(stop: Arc<AtomicBool>) {
    let bitboards: [HashSet<_>; 16] = {
        let mut bitboards = std::array::from_fn(|_| HashSet::new());
        for square in BoardSquare::all_squares() {
            bitboards[bitboard::bitboard::bishop_magic_bitboard_index(square)]
                .extend(keys_from_mask(Bitboard::bishop_possible_blockers(square)));
        }
        bitboards
    };
    let mut known_magics =
        load_magics_from_file::<16>("bishop_magics.bin").expect("Failed to read bishop magics");
    println!("Loaded current bishop magics: {known_magics:?}");
    let (magics_sender, magics_receiver) =
        std::sync::mpsc::sync_channel::<((u64, usize), usize)>(16);
    let mut rng = SmallRng::from_entropy();
    let mut handles = Vec::new();
    for (board_number, keys) in bitboards.into_iter().enumerate() {
        let initial_key = rng.gen::<u64>();
        let stop = stop.clone();
        let magics_sender = magics_sender.clone();
        handles.push(thread::spawn(move || {
            for (magic_number, key_length) in magic_number_search(initial_key, known_magics[board_number].1, keys, stop) {
                println!("Found new magic number of bishop bitboard {board_number}:\n0x{magic_number:X} (key length: {key_length})");
                magics_sender.send(((magic_number, key_length), board_number)).expect("Failed to send magic number");
            }
        }));
    }
    std::mem::drop(magics_sender);
    while let Ok((magic, board_number)) = magics_receiver.recv() {
        known_magics[board_number] = magic;
    }
    println!("Saving new bishop magics: {known_magics:?}");
    save_magics_to_file("bishop_magics.bin", known_magics).expect("Failed to save bishop magics");
    println!(
        "New Bishop magics size: {:.1}MB",
        known_magics
            .into_iter()
            .map(|(_, key_length)| 1 << (key_length + 3))
            .sum::<usize>() as f32
            / (1 << 20) as f32
    );
}

fn main() {
    let stop = Arc::new(AtomicBool::new(false));
    let bishop = thread::spawn({
        let stop = stop.clone();
        move || find_bishop_magics(stop)
    });
    let rook = thread::spawn({
        let stop = stop.clone();
        move || find_rook_magics(stop)
    });
    // TODO Use signals to decide when to be done
    thread::sleep(Duration::from_secs(60));
    println!("Stopping threads");
    stop.store(true, std::sync::atomic::Ordering::Relaxed);
    if let Err(e) = bishop.join() {
        eprintln!("Bishop task exited with error: {e:?}");
    }
    if let Err(e) = rook.join() {
        eprintln!("Rook task exited with error: {e:?}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keys_from_mask() {
        #[track_caller]
        fn check_mask(mask: Bitboard) {
            let keys = keys_from_mask(mask).collect::<Vec<Bitboard>>();
            assert_eq!(keys.len(), 1 << mask.0.count_ones(), "Wrong number of keys");
            for key in keys {
                assert!(
                    mask.contains(key),
                    "Key {key:?} not contained in mask {mask:?}"
                );
            }
        }
        check_mask(Bitboard::rook_possible_blockers(board::BoardSquare::A1));
        check_mask(Bitboard::bishop_possible_blockers(board::BoardSquare::A1));
        check_mask(Bitboard::bishop_possible_blockers(board::BoardSquare::C3));
    }
}
