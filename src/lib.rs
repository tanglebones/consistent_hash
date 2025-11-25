
// ported from https://arxiv.org/pdf/2403.18682

/// Trait for deterministic 64-bit RNGs used by `jump_back_hash`.
pub trait Random64 {
    /// Re-initialize the generator with the given seed.
    fn reset_with_seed(&mut self, seed: u64);
    /// Return the next 64-bit value.
    fn next_long(&mut self) -> u64;
}

/// Simple deterministic 64-bit RNG (SplitMix64) to mirror Java-like `nextLong` behavior.
/// Provides `reset_with_seed` and `next_long` similar to the Java snippet's API.
struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
}

impl Random64 for SplitMix64 {
    fn reset_with_seed(&mut self, seed: u64) {
        self.state = seed;
    }
    fn next_long(&mut self) -> u64 {
        // Standard SplitMix64 step
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// Port of the given Java method:
///
/// ```java
/// int jumpBackHash(long k, int n) { ... }
/// ```
///
/// Rust version keeps the same logic and bit‑level behavior. It uses a small
/// deterministic RNG to provide `next_long()` values.
pub fn jump_back_hash_with_rng<R: Random64>(k: u64, n: u32, rng: &mut R) -> u32 {
    if n <= 1 {
        return 0;
    }

    rng.reset_with_seed(k);
    let v = rng.next_long();

    // mask = ~0 >>> numberOfLeadingZeros(n-1)  (Java int semantics)
    let n_minus_1 = n - 1;
    let mask: u32 = (!0u32) >> n_minus_1.leading_zeros();

    // u = (int) (v ^ (v >>> 32)) & mask
    let u: u32 = ((v ^ (v >> 32)) as u32) & mask;

    let mut u_work = u;
    while u_work != 0 {
        // q = 1 << ~numberOfLeadingZeros(u)  (equivalent to highest power of two <= u)
        let q: u32 = 1u32 << (31 - u_work.leading_zeros());

        // b = q + ((int)(v >>> (bitCount(u) << 5)) & (q - 1))
        let shift: u32 = ((u_work.count_ones() << 5) & 63) as u32; // Java long >>> masks by 63
        let b0: u32 = ((v >> shift) as u32) & (q - 1);
        let mut b: u32 = q.wrapping_add(b0);

        // Inner loop
        loop {
            if b < n {
                return b;
            }
            let w = rng.next_long();

            // mask (q<<1)-1 with care when q == 1<<31
            let mask2: u32 = if q == 0x8000_0000 { 0xFFFF_FFFF } else { (q << 1) - 1 };

            b = (w as u32) & mask2;
            if b < q {
                break; // exit inner loop
            }
            if b < n {
                return b;
            }
            b = ((w >> 32) as u32) & mask2;
            if b < q {
                break; // exit inner loop
            }
            if b < n {
                return b;
            }
            // Otherwise, continue the inner loop to draw another `w`
        }

        // Clear the current highest bit and continue
        u_work ^= q;
    }

    0
}

/// Convenience wrapper that uses `SplitMix64` as the RNG implementation
/// to preserve the original API.
pub fn jump_back_hash(k: u64, n: u32) -> u32 {
    let mut rng = SplitMix64::new(0);
    jump_back_hash_with_rng(k, n, &mut rng)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn jump_back_hash_trivial_cases() {
        assert_eq!(jump_back_hash(0, 0), 0);
        assert_eq!(jump_back_hash(0, 1), 0);
        assert_eq!(jump_back_hash(1, 1), 0);
        assert_eq!(jump_back_hash(1, 1), 0);
        assert_eq!(jump_back_hash(0, 2), 0);
        assert_eq!(jump_back_hash(1, 2), 1);
    }

    #[test]
    fn jump_back_hash_in_range() {
        // Check many seeds and n that result is either 0 or < n
        for n in [2u32, 3, 4, 7, 16, 31, 32, 33, 1000] {
            for k in [0u64, 1, 2, 123456789, u64::MAX - 1, u64::MAX] {
                let r = jump_back_hash(k, n);
                assert!(r == 0 || r < n, "k={k}, n={n}, r={r}");
            }
        }
    }
}
