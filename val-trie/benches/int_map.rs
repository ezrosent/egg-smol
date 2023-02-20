use std::hash::BuildHasherDefault;

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use hashbrown::HashMap;
use rand::{distributions::Uniform, prelude::Distribution};
use rustc_hash::FxHasher;
use val_trie::IntMap;

fn lookup_test<M: MapLike>(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("Lookups (Dense, {})", M::NAME));
    let mut rng = rand::thread_rng();
    const BATCH_SIZE: usize = 1024;
    for map_size in [1u64 << 10, 1 << 17, 1 << 25] {
        let mut map = M::default();
        for i in 0..map_size {
            map.add(i, i);
        }

        group.throughput(Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(format!("hits, size={map_size}"), &map, |b, i| {
            let mut elts = Vec::with_capacity(BATCH_SIZE);
            let between = Uniform::from(0..map_size);
            for _ in 0..BATCH_SIZE {
                elts.push(between.sample(&mut rng));
            }
            b.iter(|| {
                for elt in &elts {
                    black_box(i.lookup(*elt));
                }
            })
        });
        group.bench_with_input(format!("misses, size={map_size}"), &map, |b, i| {
            let mut elts = Vec::with_capacity(BATCH_SIZE);
            let between = Uniform::from(map_size..u64::MAX);
            for _ in 0..BATCH_SIZE {
                elts.push(between.sample(&mut rng));
            }
            b.iter(|| {
                for elt in &elts {
                    black_box(i.lookup(*elt));
                }
            })
        });
    }
}

// Benchmarks:
// * sparse lookups
// * test hashmap (where the map in question is a key) lookups (no sharing, some sharing)
// * test insertions (similar to lookups: dense and sparse)

trait MapLike: Clone + Eq + Default {
    const NAME: &'static str;
    fn add(&mut self, k: u64, v: u64);
    fn lookup(&self, k: u64) -> bool;
}

criterion_group!(
    benches,
    lookup_test::<HashBrown>,
    lookup_test::<ImMap>,
    lookup_test::<ValTrie>,
);

criterion_main!(benches);

type ValTrie = IntMap<u64, BuildHasherDefault<FxHasher>>;
type HashBrown = HashMap<u64, u64, BuildHasherDefault<FxHasher>>;
type ImMap = im::HashMap<u64, u64, BuildHasherDefault<FxHasher>>;

impl MapLike for ValTrie {
    const NAME: &'static str = "int-map";
    fn add(&mut self, k: u64, v: u64) {
        self.insert(k, v);
    }

    fn lookup(&self, k: u64) -> bool {
        self.contains_key(k)
    }
}

impl MapLike for HashBrown {
    const NAME: &'static str = "hashbrown";
    fn add(&mut self, k: u64, v: u64) {
        self.insert(k, v);
    }

    fn lookup(&self, k: u64) -> bool {
        self.contains_key(&k)
    }
}

impl MapLike for ImMap {
    const NAME: &'static str = "im";
    fn add(&mut self, k: u64, v: u64) {
        self.insert(k, v);
    }

    fn lookup(&self, k: u64) -> bool {
        self.contains_key(&k)
    }
}
