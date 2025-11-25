
// ported from https://arxiv.org/pdf/2403.18682

/// Trait for deterministic 64-bit RNGs used by `hash`.
pub trait Random64 {
    /// Re-initialize the generator with the given seed.
    fn reset_with_seed(&mut self, seed: u64);
    /// Return the next 64-bit value.
    fn next_long(&mut self) -> u64;
}

/// Trait for consistent hashing implementors.
/// Implementations must deterministically map a key `k` to a bucket in `[0, n)`.
pub trait ConsistentHasher {
    fn hash(&mut self, k: u64, n: u32) -> u32;
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
pub fn hash_with_rng<R: Random64>(k: u64, n: u32, rng: &mut R) -> u32 {
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

/// Stateful hasher that owns a pluggable RNG implementing `Random64` and provides `hash` as a method.
pub struct JumpBackHasher<R: Random64> {
    rng: R,
}

impl<R: Random64> JumpBackHasher<R> {
    /// Construct a hasher from any RNG implementing `Random64`.
    pub fn from_rng(rng: R) -> Self {
        Self { rng }
    }

    /// Compute the jump-back hash for key `k` in range `[0, n)`.
    /// This method re-seeds the internal RNG with `k` for each call,
    /// matching the behavior of the free function.
    pub fn hash(&mut self, k: u64, n: u32) -> u32 {
        hash_with_rng(k, n, &mut self.rng)
    }
}

/// Convenience constructors for the default RNG `SplitMix64`.
impl JumpBackHasher<SplitMix64> {
    /// Create a new hasher with an internal SplitMix64 RNG.
    pub fn new() -> Self {
        Self { rng: SplitMix64::new(0) }
    }
}

impl<R: Random64> ConsistentHasher for JumpBackHasher<R> {
    fn hash(&mut self, k: u64, n: u32) -> u32 {
        // Delegate to inherent method
        JumpBackHasher::hash(self, k, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn jump_back_hash_trivial_cases() {
        let mut hasher = JumpBackHasher::new();
        assert_eq!(hasher.hash(0, 0), 0);
        assert_eq!(hasher.hash(0, 1), 0);
        assert_eq!(hasher.hash(1, 1), 0);
        assert_eq!(hasher.hash(1, 1), 0);
        assert_eq!(hasher.hash(0, 2), 0);
        assert_eq!(hasher.hash(1, 2), 1);
    }

    #[test]
    fn jump_back_hash_in_range() {
        // Check many seeds and n that result is either 0 or < n
        let mut hasher = JumpBackHasher::new();
        for n in [2u32, 3, 4, 7, 16, 31, 32, 33, 1000] {
            for k in [0u64, 1, 2, 123456789, u64::MAX - 1, u64::MAX] {
                let r = hasher.hash(k, n);
                assert!(r == 0 || r < n, "k={k}, n={n}, r={r}");
            }
        }
    }

    #[test]
    fn jump_back_hasher_method_works() {
        let mut hasher = JumpBackHasher::new();
        for n in [0u32, 1, 2, 3, 10, 100] {
            let mut pr = 0;
            for k in [0u64, 1, 2, 123456789, u64::MAX] {
                let r = hasher.hash(k, n);
                assert!(r == 0 || r < n || pr <= r, "method: k={k}, n={n}, pr={pr}, r={r}");
                pr = r;
            }
        }
    }
}


