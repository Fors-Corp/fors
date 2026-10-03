//! The one source of randomness in this crate: a seeded SplitMix64 stream
//! (`fors_index::splitmix64` as the output mix). Every generator choice and
//! every reducer ordering draws from one of these, so a seed reproduces a
//! program or a reduction exactly.

pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng { state: seed }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        fors_index::splitmix64(self.state)
    }

    /// Uniform-enough in `0..n` (`0` when `n == 0`).
    pub fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next_u64() % n }
    }

    /// A Fisher-Yates shuffle of `xs`.
    pub fn shuffle<T>(&mut self, xs: &mut [T]) {
        for i in (1..xs.len()).rev() {
            let j = self.below(i as u64 + 1) as usize;
            xs.swap(i, j);
        }
    }
}
