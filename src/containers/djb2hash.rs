// SPDX-License-Identifier: Apache-2.0

use core::hash::Hasher;

/// Simple hasher for the djb2 algorithm.
pub(crate) struct Djb2Hasher {
    hash: u64,
}

impl Djb2Hasher {
    pub fn new() -> Djb2Hasher {
        Djb2Hasher { hash: 5381 }
    }
}

impl Hasher for Djb2Hasher {
    fn finish(&self) -> u64 {
        self.hash
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.hash = self.hash.wrapping_mul(33).wrapping_add(*byte as u64);
        }
    }
}

impl Default for Djb2Hasher {
    fn default() -> Djb2Hasher {
        Djb2Hasher::new()
    }
}
