// ported from https://arxiv.org/pdf/2403.18682

/// Trait for deterministic 64-bit RNGs used by `hash`.
pub trait Random64 {
  /// Create a new generator with a seed of 0.
  fn new() -> Self;
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
pub struct SplitMix64 {
  state: u64,
}

impl SplitMix64 {
  fn from_seed(seed: u64) -> Self {
    Self { state: seed }
  }
}

impl Default for SplitMix64 {
  fn default() -> Self {
    SplitMix64::from_seed(0)
  }
}

impl Random64 for SplitMix64 {
  fn new() -> Self {
    Self::default()
  }
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

/// Stateful hasher that owns a pluggable RNG implementing `Random64` and provides `hash` as a method.
pub struct JumpBackConsistentHasher<R: Random64 = SplitMix64> {
  rng: R,
}

impl<R: Random64> JumpBackConsistentHasher<R> {
  pub fn new_with_rng(rng: R) -> Self {
    Self { rng }
  }
  /// Construct a hasher from any RNG implementing `Random64`.
  pub fn from_rng(rng: R) -> Self {
    Self { rng }
  }

  /// Compute the jump-back hash for key `k` in range `[0, n)`.
  /// This method re-seeds the internal RNG with `k` for each call,
  /// matching the behavior of the free function.
  pub fn hash(&mut self, k: u64, n: u32) -> u32 {
    if n <= 1 {
      return 0;
    }

    self.rng.reset_with_seed(k);
    let v = self.rng.next_long();

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
        let w = self.rng.next_long();

        // mask (q<<1)-1 with care when q == 1<<31
        let mask2: u32 = if q == 0x8000_0000 {
          0xFFFF_FFFF
        } else {
          (q << 1) - 1
        };

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
}

impl<R: Random64> ConsistentHasher for JumpBackConsistentHasher<R> {
  fn hash(&mut self, k: u64, n: u32) -> u32 {
    // Delegate to inherent method
    JumpBackConsistentHasher::hash(self, k, n)
  }
}

impl JumpBackConsistentHasher<SplitMix64> {
  pub fn new() -> Self {
    Self {
      rng: SplitMix64::new(),
    }
  }
}

pub struct JumpConsistentHasher;

impl JumpConsistentHasher {
  pub fn new() -> Self {
    Self
  }
}

impl ConsistentHasher for JumpConsistentHasher {
  fn hash(&mut self, k: u64, n: u32) -> u32 {
    if n <= 1 {
      return 0;
    }
    let mut key: u64 = k;
    let mut b: i64 = -1;
    let mut j: i64 = 0;
    let nb = n as i64;
    while j < nb {
      b = j;
      // key = key * 2862933555777941757ULL + 1;  // with wrapping semantics
      key = key.wrapping_mul(2862933555777941757u64).wrapping_add(1);
      // j = (b + 1) * (double(1LL << 31) / double((key >> 33) + 1));
      let denom = ((key >> 33) + 1) as f64;
      let x = ((b + 1) as f64) * ((1u64 << 31) as f64 / denom);
      j = x as i64;
    }
    b as u32
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn trivial_cases() {
    let mut jbh = JumpBackConsistentHasher::new();
    let mut jh = JumpConsistentHasher::new();
    assert_eq!(jbh.hash(0, 0), 0);
    assert_eq!(jbh.hash(0, 1), 0);
    assert_eq!(jbh.hash(1, 1), 0);
    assert_eq!(jbh.hash(1, 1), 0);
    assert_eq!(jbh.hash(0, 2), 0);
    assert_eq!(jbh.hash(1, 2), 1);

    assert_eq!(jh.hash(0, 0), 0);
    assert_eq!(jh.hash(0, 1), 0);
    assert_eq!(jh.hash(1, 1), 0);
    assert_eq!(jh.hash(1, 1), 0);
    assert_eq!(jh.hash(0, 2), 0);
    assert_eq!(jh.hash(1, 2), 1);
  }

  #[test]
  fn hash_in_range() {
    // Check many seeds and n that result is either 0 or < n
    let mut jbh = JumpBackConsistentHasher::new();
    let mut jh = JumpConsistentHasher::new();

    for n in [2u32, 3, 4, 7, 16, 31, 32, 33, 1000] {
      for k in [0u64, 1, 2, 123456789, u64::MAX - 1, u64::MAX] {
        {
          let r = jbh.hash(k, n);
          assert!(r == 0 || r < n, "k={k}, n={n}, r={r}");
        }
        {
          let r = jh.hash(k, n);
          assert!(r == 0 || r < n, "k={k}, n={n}, r={r}");
        }
      }
    }
  }

  #[test]
  fn buckets_move_forward() {
    let mut jbh = JumpBackConsistentHasher::new();
    let mut jh = JumpConsistentHasher::new();
    for n in [0u32, 1, 2, 3, 10, 100] {
      let mut pr_jb = 0;
      let mut pr_j = 0;
      for k in [0u64, 1, 2, 123456789, u64::MAX] {
        {
          let r = jbh.hash(k, n);
          assert!(
            r == 0 || r < n || pr_jb <= r,
            "jbh: k={k}, n={n}, pr={pr_jb}, r={r}"
          );
          pr_jb = r;
        }
        {
          let r = jh.hash(k, n);
          assert!(
            r == 0 || r < n || pr_j <= r,
            "jh: k={k}, n={n}, pr={pr_j}, r={r}"
          );
          pr_j = r;
        }
      }
    }
  }

  #[test]
  fn entries_evenly_distributed() {
    let mut jbh = JumpBackConsistentHasher::new();
    let mut jh = JumpConsistentHasher::new();
    const BUCKET_COUNT: usize = 1024;

    let mut jb_counts = [0u32; BUCKET_COUNT];
    let mut j_counts = [0u32; BUCKET_COUNT];
    const FACTOR: usize = 10000;
    const ENTRIES: usize = BUCKET_COUNT * FACTOR;
    for k in 0..ENTRIES {
      let i = jbh.hash(k as u64, BUCKET_COUNT as u32) as usize;
      jb_counts[i] += 1;
      let i = jh.hash(k as u64, BUCKET_COUNT as u32) as usize;
      j_counts[i] += 1;
    }

    {
      let mut min = u32::MAX;
      let mut max = 0;

      for c in jb_counts {
        min = min.min(c);
        max = max.max(c);
      }
      // println!("jbh: min={min}, max={max}");
      assert!(min >= (FACTOR * 95 / 100) as u32 && min <= (FACTOR * 105 / 100) as u32);
    }
    {
      let mut min = u32::MAX;
      let mut max = 0;

      for c in j_counts {
        min = min.min(c);
        max = max.max(c);
      }
      // println!("jh: min={min}, max={max}");
      assert!(min >= (FACTOR * 95 / 100) as u32 && min <= (FACTOR * 105 / 100) as u32);
    }

  }
}
