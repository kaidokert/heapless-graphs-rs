// SPDX-License-Identifier: Apache-2.0

use core::hash::{Hash, Hasher};

use super::SetTrait;
use crate::containers::djb2hash::Djb2Hasher;

/// A minimal set implementation without any collision handling
#[derive(Debug)]
pub struct Set<K, const N: usize> {
    keys: [Option<K>; N],
}

impl<K: Eq + Hash, const N: usize> Set<K, N> {
    fn hash_key(&self, key: &K) -> usize {
        let mut hasher = Djb2Hasher::default();
        key.hash(&mut hasher);
        (hasher.finish() as usize) % N
    }
    fn find_key_with_hash(&self, key: &K) -> (bool, usize) {
        let hash = self.hash_key(key);
        if let Some(stored_key) = &self.keys[hash] {
            (stored_key == key, hash)
        } else {
            (false, hash)
        }
    }
}

impl<K: Eq + Hash, const N: usize> Default for Set<K, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Eq + Hash, const N: usize> SetTrait<K> for Set<K, N> {
    fn new() -> Self
    where
        Self: Sized,
    {
        Self {
            keys: core::array::from_fn(|_| None),
        }
    }

    fn insert(&mut self, key: K) -> bool {
        let (exists, hash) = self.find_key_with_hash(&key);
        if !exists {
            self.keys[hash] = Some(key);
        }
        !exists
    }

    fn remove(&mut self, key: &K) -> bool {
        let (exists, hash) = self.find_key_with_hash(key);
        if exists {
            self.keys[hash] = None;
        }
        exists
    }

    fn contains(&self, key: &K) -> bool {
        self.find_key_with_hash(key).0
    }

    fn len(&self) -> usize {
        self.keys.iter().filter(|k| k.is_some()).count()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn clear(&mut self) {
        self.keys.fill_with(|| None);
    }
}
