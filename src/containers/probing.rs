// SPDX-License-Identifier: Apache-2.0

//! Shared linear probing logic for hash tables with collision tracking

use core::hash::{Hash, Hasher};
use core::sync::atomic::{AtomicUsize, Ordering};

use super::djb2hash::Djb2Hasher;

/// Trait for slot types that can be used in linear probing hash tables
pub trait ProbableSlot<K> {
    /// Returns true if this slot contains the given key
    fn contains_key(&self, key: &K) -> bool
    where
        K: Eq;

    /// Returns true if this slot is empty (never used)
    fn is_empty(&self) -> bool;

    /// Returns true if this slot is a tombstone (previously occupied, now deleted)
    fn is_tombstone(&self) -> bool;
}

/// Computes the hash for a key and returns the initial index
pub fn hash_key<K: Hash, const N: usize>(key: &K) -> usize {
    let mut hasher = Djb2Hasher::default();
    key.hash(&mut hasher);
    (hasher.finish() as usize) % N
}

/// Generic linear probing implementation that works with any slot type
///
/// Returns (found, index) where:
/// - found: true if the key was found in an occupied slot
/// - index: either the slot containing the key, or an appropriate slot for insertion
pub fn find_key_with_hash<K, S, const N: usize>(
    slots: &[S; N],
    key: &K,
    collision_count: &AtomicUsize,
) -> (bool, usize)
where
    K: Eq + Hash,
    S: ProbableSlot<K>,
{
    let start_hash = hash_key::<K, N>(key);
    let mut index = start_hash;
    let mut first_tombstone = None;

    for i in 0..N {
        let slot = &slots[index];

        if slot.contains_key(key) {
            return (true, index); // Key found
        } else if slot.is_empty() {
            // Return the first tombstone (if any) or this empty slot
            return (false, first_tombstone.unwrap_or(index));
        } else if slot.is_tombstone() {
            // Track the first tombstone for potential insertion
            if first_tombstone.is_none() {
                first_tombstone = Some(index);
            }
            // Collision: tombstone counts as occupied for probing
            if i > 0 {
                collision_count.fetch_add(1, Ordering::Relaxed);
            }
        } else {
            // Slot is occupied with a different key - collision
            if i > 0 {
                collision_count.fetch_add(1, Ordering::Relaxed);
            }
        }

        index = (index + 1) % N; // Linear probing: move to next slot
        if index == start_hash {
            // Full cycle, array is full (or all tombstones)
            return (false, first_tombstone.unwrap_or(start_hash));
        }
    }
    (false, first_tombstone.unwrap_or(start_hash)) // Fallback
}
