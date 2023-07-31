//! Take the magic numbers found and turn them into attack tables

use bitboard::Bitboard;
use board::{BoardSquare, BoardSquareOffset};

use std::{
    fs,
    io::{self, Write},
    mem,
    path::Path,
};

/// Load the bitboards stored in the indicated file.
///
/// If the file does not exist, make a new file with a magic number of 1 and a size of 64 bits.
/// This size is guaranteed valid, but will be far too large to fit in a computer, so you should
/// search.
fn load_magics_from_file<const N: usize>(path: impl AsRef<Path>) -> io::Result<[(u64, usize); N]> {
    let read = fs::read(path)?;
    let mut data = mem::MaybeUninit::<[(u64, usize); N]>::uninit();
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

/// The data per board in the attack table
#[derive(Copy, Clone, Default)]
struct PerBoardData {
    /// The magic number by which to multiply
    magic_number: u64,
    /// The number of bits to shift after multiplying
    shift: usize,
    /// The index into the table at which to start indexing for this board
    table_offset_begin: usize,
}

/// An entire attack table
///
/// `N` is the number of boards, which is 16 for bishops and 32 for rooks
struct AttackTable<const N: usize> {
    /// The per-bitboard data (instructions for indexing into this table)
    per_board: [PerBoardData; N],
    /// The table of bitboards for possible attacks
    table: Vec<Bitboard>,
}
impl<const N: usize> AttackTable<N> {
    /// Write this table to the given file on disk
    fn write_table(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let mut file = fs::File::create(path)?;
        file.write_all(unsafe {
            std::slice::from_raw_parts(
                self.per_board.as_ptr().cast::<u8>(),
                mem::size_of::<[PerBoardData; N]>(),
            )
        })?;
        file.write_all(unsafe {
            std::slice::from_raw_parts(
                self.table.as_ptr().cast::<u8>(),
                self.table.len() * mem::size_of::<Bitboard>(),
            )
        })?;
        file.sync_all()?;
        Ok(())
    }

    /// Get the amount of size taken up when written to disk
    fn disk_size(&self) -> usize {
        mem::size_of::<[PerBoardData; N]>() + self.table.len() * mem::size_of::<Bitboard>()
    }

    /// Returns the portion of the attack table which is used
    fn used_fraction(&self) -> f32 {
        let used = self.table.iter().filter(|board| !board.is_empty()).count();
        used as f32 / self.table.len() as f32
    }
}

/// The attack table for bishops
type BishopAttackTable = AttackTable<16>;
/// The attack table for rooks
type RookAttackTable = AttackTable<32>;

/// Make the [`BishopAttackTable`] for the given set of magics
fn make_rook_attack_table(magics: [(u64, usize); 32]) -> RookAttackTable {
    fn slow_rook_moves(source: BoardSquare, blockers: Bitboard) -> Bitboard {
        let mut newly_threatened = Bitboard::empty();
        for offset in [
            BoardSquareOffset::from_rank_file(1, 0),
            BoardSquareOffset::from_rank_file(-1, 0),
            BoardSquareOffset::from_rank_file(0, 1),
            BoardSquareOffset::from_rank_file(0, -1),
        ] {
            let mut new_square = source;
            while new_square.is_valid() {
                new_square = offset.offset(new_square);
                newly_threatened |= Bitboard::from(new_square);
                if blockers.intersects(Bitboard::from(new_square)) {
                    break;
                }
            }
        }
        newly_threatened
    }
    let mut table = Vec::new();
    let mut per_board = [PerBoardData::default(); 32];
    for (index, (per_board, (magic_number, key_size))) in
        per_board.iter_mut().zip(magics.into_iter()).enumerate()
    {
        let shift = 64 - key_size;
        per_board.magic_number = magic_number;
        per_board.shift = shift;
        per_board.table_offset_begin = table.len();
        for square in BoardSquare::all_squares() {
            if bitboard::bitboard::bishop_magic_bitboard_index(square) != index {
                continue;
            }
            for key in keys_from_mask(Bitboard::bishop_possible_blockers(square)) {
                let index = ((key.0 * magic_number) >> per_board.shift) as usize
                    + per_board.table_offset_begin;
                if index >= table.len() {
                    table.resize_with(index + 1, Bitboard::empty);
                }
                table[index] |= slow_rook_moves(square, key);
            }
        }
    }
    RookAttackTable { table, per_board }
}

/// Make the [`BishopAttackTable`] for the given set of magics
fn make_bishop_attack_table(magics: [(u64, usize); 16]) -> BishopAttackTable {
    fn slow_bishop_moves(source: BoardSquare, blockers: Bitboard) -> Bitboard {
        let mut newly_threatened = Bitboard::empty();
        for offset in [
            BoardSquareOffset::from_rank_file(1, 1),
            BoardSquareOffset::from_rank_file(1, -1),
            BoardSquareOffset::from_rank_file(-1, 1),
            BoardSquareOffset::from_rank_file(-1, -1),
        ] {
            let mut new_square = source;
            while new_square.is_valid() {
                new_square = offset.offset(new_square);
                newly_threatened |= Bitboard::from(new_square);
                if blockers.intersects(Bitboard::from(new_square)) {
                    break;
                }
            }
        }
        newly_threatened
    }
    let mut table = Vec::new();
    let mut per_board = [PerBoardData::default(); 16];
    for (index, (per_board, (magic_number, key_size))) in
        per_board.iter_mut().zip(magics.into_iter()).enumerate()
    {
        let shift = 64 - key_size;
        per_board.magic_number = magic_number;
        per_board.shift = shift;
        per_board.table_offset_begin = table.len();
        for square in BoardSquare::all_squares() {
            if bitboard::bitboard::bishop_magic_bitboard_index(square) != index {
                continue;
            }
            for key in keys_from_mask(Bitboard::bishop_possible_blockers(square)) {
                let index = ((key.0 * magic_number) >> per_board.shift) as usize
                    + per_board.table_offset_begin;
                if index >= table.len() {
                    table.resize_with(index + 1, Bitboard::empty);
                }
                table[index] |= slow_bishop_moves(square, key);
            }
        }
    }
    BishopAttackTable { table, per_board }
}

fn main() {
    let bishop_magics =
        load_magics_from_file("bishop_magics.bin").expect("Failed to load bishop magics");
    let bishop_attack_table = make_bishop_attack_table(bishop_magics);
    bishop_attack_table
        .write_table("bishop_attacks.bin")
        .expect("Failed to write bishop attack table");
    println!(
        "Bishop table written ({:.1}MB, {:.2}% used)",
        bishop_attack_table.disk_size() as f32 / (1 << 20) as f32,
        bishop_attack_table.used_fraction() * 100.0
    );
    let rook_magics =
        load_magics_from_file("rook_magics.bin").expect("Failed to load bishop magics");
    let rook_attack_table = make_rook_attack_table(rook_magics);
    rook_attack_table
        .write_table("rook_attacks.bin")
        .expect("Failed to write rook attack table");
    println!(
        "Rook table written ({:.1}MB, {:.2}% used)",
        rook_attack_table.disk_size() as f32 / (1 << 20) as f32,
        rook_attack_table.used_fraction() * 100.0
    );
}
