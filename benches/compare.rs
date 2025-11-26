use consistent_hash::{ConsistentHasher, JumpBackConsistentHasher, JumpConsistentHasher};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::time::Duration;

fn bench_compare(c: &mut Criterion) {
  // Pre-generate a fixed set of keys so we don't measure key generation.
  let num_keys: usize = 100_000;
  let mut keys = Vec::with_capacity(num_keys);
  // Simple deterministic sequence of u64 keys.
  let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
  for _ in 0..num_keys {
    // SplitMix64-like progression for key generation (not the hasher's RNG), deterministic.
    x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^= z >> 31;
    keys.push(z);
  }

  let mut group = c.benchmark_group("consistent_hash_vs_jump");
  // Try a range of bucket counts
  for &n in &[16u32, 64, 256, 1024, 4096, 65_536] {
    // JumpBackConsistentHasher (SplitMix64-based)
    group.bench_with_input(BenchmarkId::new("JumpBack", n), &n, |b, &n| {
      b.iter(|| {
        let mut hasher = JumpBackConsistentHasher::new();
        let mut sum: u64 = 0; // accumulate to avoid optimizing away
        for &k in &keys {
          let r = ConsistentHasher::hash(&mut hasher, k, n);
          sum = sum.wrapping_add(r as u64);
        }
        std::hint::black_box(sum)
      });
    });

    // JumpConsistentHasher (C reference)
    group.bench_with_input(BenchmarkId::new("Jump", n), &n, |b, &n| {
      b.iter(|| {
        let mut hasher = JumpConsistentHasher::new();
        let mut sum: u64 = 0;
        for &k in &keys {
          let r = ConsistentHasher::hash(&mut hasher, k, n);
          sum = sum.wrapping_add(r as u64);
        }
        std::hint::black_box(sum)
      });
    });
  }
  group.finish();
}

criterion_group!(name = benches; config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(30)); targets = bench_compare);
criterion_main!(benches);
