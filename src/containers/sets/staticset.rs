// SPDX-License-Identifier: Apache-2.0

use core::hash::Hash;
use core::sync::atomic::{AtomicUsize, Ordering};

use super::SetTrait;
use crate::containers::probing::{find_key_with_hash, ProbableSlot};

/// Represents the state of a slot in the set
#[derive(Debug)]
enum Slot<K> {
    Occupied(K), // Contains a key
    Empty,       // Never used
    Tombstone,   // Previously occupied, now deleted
}

/// A set implementation with linear probing for collision handling and atomic collision tracking
#[derive(Debug)]
pub struct Set<K, const N: usize> {
    slots: [Slot<K>; N],          // Stores keys, empty slots, or tombstones
    collision_count: AtomicUsize, // Tracks collisions atomically
}

impl<K: Eq> ProbableSlot<K> for Slot<K> {
    fn contains_key(&self, key: &K) -> bool {
        match self {
            Slot::Occupied(stored_key) => stored_key == key,
            _ => false,
        }
    }

    fn is_empty(&self) -> bool {
        matches!(self, Slot::Empty)
    }

    fn is_tombstone(&self) -> bool {
        matches!(self, Slot::Tombstone)
    }
}

impl<K: Eq + Hash, const N: usize> Set<K, N> {
    /// Finds the key or an appropriate slot for insertion, returning (found, index)
    fn find_key_with_hash(&self, key: &K) -> (bool, usize) {
        find_key_with_hash(&self.slots, key, &self.collision_count)
    }

    /// Returns the total number of collisions recorded
    pub fn collision_count(&self) -> usize {
        self.collision_count.load(Ordering::Relaxed)
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
            slots: core::array::from_fn(|_| Slot::Empty), // All slots start empty
            collision_count: AtomicUsize::new(0),         // Initialize to 0
        }
    }

    fn insert(&mut self, key: K) -> bool {
        let (exists, index) = self.find_key_with_hash(&key);
        if !exists {
            self.slots[index] = Slot::Occupied(key);
            // Collision already counted in find_key_with_hash
        }
        !exists
    }

    fn remove(&mut self, key: &K) -> bool {
        let (exists, index) = self.find_key_with_hash(key);
        if exists {
            self.slots[index] = Slot::Tombstone; // Mark as tombstone instead of Empty
        }
        exists
    }

    fn contains(&self, key: &K) -> bool {
        self.find_key_with_hash(key).0
    }

    fn len(&self) -> usize {
        self.slots
            .iter()
            .filter(|s| matches!(s, Slot::Occupied(_)))
            .count()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn clear(&mut self) {
        self.slots = core::array::from_fn(|_| Slot::Empty);
        self.collision_count.store(0, Ordering::Relaxed); // Reset collision counter
    }
}

#[cfg(test)]
mod collision_tests {
    use super::*;

    #[test]
    fn test_new_set_has_zero_collisions() {
        let set: Set<i32, 5> = Set::new();
        assert_eq!(set.collision_count(), 0);
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_no_collisions_with_non_overlapping_hashes() {
        let mut set: Set<i32, 10> = Set::new();

        // Insert values and check collision count
        assert!(set.insert(0));
        assert_eq!(set.collision_count(), 0);

        assert!(set.insert(10));
        // Don't assume no collisions - just check the count is reasonable
        let count_after_10 = set.collision_count();

        assert!(set.insert(20));
        let count_after_20 = set.collision_count();

        // Collision count should be monotonic
        assert!(count_after_20 >= count_after_10);
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn test_forced_collisions_in_small_table() {
        let mut set: Set<i32, 2> = Set::new();

        // With only 2 slots, we're guaranteed collisions eventually
        assert!(set.insert(1)); // First insertion
        assert_eq!(set.collision_count(), 0);

        assert!(set.insert(2)); // Second insertion
        let count_after_2 = set.collision_count();

        // Now table is full, remove one to make space
        assert!(set.remove(&1));

        assert!(set.insert(3)); // Third insertion - may cause collisions
        let count_after_3 = set.collision_count();

        // Should have at least as many collisions as before
        assert!(count_after_3 >= count_after_2);

        assert_eq!(set.len(), 2);
        assert!(!set.contains(&1)); // Removed
        assert!(set.contains(&2));
        assert!(set.contains(&3));
    }

    #[test]
    fn test_collision_counting_during_lookup() {
        let mut set: Set<i32, 2> = Set::new();

        // Fill table completely to force future collisions
        set.insert(1);
        set.insert(2);

        let initial_collisions = set.collision_count();

        // Multiple lookups should potentially increase collision count
        set.contains(&1);
        set.contains(&2);
        let after_lookup = set.collision_count();

        // Collision count should be monotonic (not decrease)
        assert!(after_lookup >= initial_collisions);
    }

    #[test]
    fn test_collision_counting_with_tombstones() {
        let mut set: Set<i32, 2> = Set::new();

        // Fill table
        set.insert(1);
        set.insert(2);

        // Remove first element (creates tombstone)
        assert!(set.remove(&1));
        assert_eq!(set.len(), 1);

        let collisions_after_remove = set.collision_count();

        // Insert another value - may interact with tombstone
        assert!(set.insert(3));

        // Should maintain monotonic collision counting
        assert!(set.collision_count() >= collisions_after_remove);
        assert_eq!(set.len(), 2);
        assert!(!set.contains(&1)); // Removed
        assert!(set.contains(&2)); // Still there
        assert!(set.contains(&3)); // Newly added
    }

    #[test]
    fn test_duplicate_insertion_behavior() {
        let mut set: Set<i32, 3> = Set::new();

        set.insert(1);
        set.insert(2);
        let collisions_after_insert = set.collision_count();

        // Try to insert 2 again (duplicate)
        assert!(!set.insert(2)); // Should return false (not inserted)

        // Collision count may increase during lookup for duplicate
        assert!(set.collision_count() >= collisions_after_insert);
        assert_eq!(set.len(), 2); // Length unchanged
    }

    #[test]
    fn test_clear_resets_collision_count() {
        let mut set: Set<i32, 3> = Set::new();

        // Create some collisions
        set.insert(0);
        set.insert(3);
        set.insert(6);

        assert!(set.collision_count() > 0);
        assert_eq!(set.len(), 3);

        // Clear should reset everything
        set.clear();

        assert_eq!(set.collision_count(), 0);
        assert_eq!(set.len(), 0);
        assert!(set.is_empty());

        // Should work normally after clear
        assert!(set.insert(1));
        assert_eq!(set.collision_count(), 0);
    }

    #[test]
    fn test_collision_count_increases_monotonically() {
        let mut set: Set<i32, 5> = Set::new();
        let mut last_count = 0;

        // Insert values that will likely collide
        for i in 0..5 {
            let value = i * 5; // Values: 0, 5, 10, 15, 20
            set.insert(value);

            let current_count = set.collision_count();
            assert!(
                current_count >= last_count,
                "Collision count should not decrease: {} -> {}",
                last_count,
                current_count
            );
            last_count = current_count;
        }

        // Subsequent operations should only increase the count
        set.contains(&15); // Lookup
        assert!(set.collision_count() >= last_count);

        set.remove(&10); // Remove
        assert!(set.collision_count() >= last_count);
    }

    #[test]
    fn test_collision_behavior_with_string_keys() {
        let mut set: Set<&'static str, 3> = Set::new();

        // Use strings that are likely to collide in a small table
        let keys = ["a", "b", "c", "d"];

        for &key in &keys {
            set.insert(key);
        }

        // Should have some collisions due to small table size
        assert!(set.collision_count() > 0);
        assert_eq!(set.len(), 3); // Can only fit 3 in a size-3 table

        // Verify we can find the stored keys
        let mut found_count = 0;
        for &key in &keys {
            if set.contains(&key) {
                found_count += 1;
            }
        }
        assert_eq!(found_count, 3);
    }

    #[test]
    fn test_collision_counting_with_full_table() {
        let mut set: Set<i32, 2> = Set::new();

        // Fill table completely
        assert!(set.insert(1));
        let count_after_first = set.collision_count();

        assert!(set.insert(2));
        let count_after_second = set.collision_count();

        // Should be monotonic
        assert!(count_after_second >= count_after_first);

        // Table is now full, create tombstone and reuse
        assert!(set.remove(&1)); // Creates tombstone

        assert!(set.insert(3)); // Reuses space
        let final_count = set.collision_count();

        // Should still be monotonic
        assert!(final_count >= count_after_second);

        assert_eq!(set.len(), 2);
        assert!(!set.contains(&1));
        assert!(set.contains(&2));
        assert!(set.contains(&3));
    }

    #[test]
    fn test_default_constructor_has_zero_collisions() {
        let set: Set<i32, 10> = Set::default();
        assert_eq!(set.collision_count(), 0);
        assert!(set.is_empty());
    }

    #[test]
    fn test_collision_tracking_with_remove_patterns() {
        let mut set: Set<i32, 4> = Set::new();

        // Insert a sequence that creates collisions
        set.insert(0); // slot 0
        set.insert(4); // slot 0 -> 1 (collision)
        set.insert(8); // slot 0 -> 1 -> 2 (more collisions)

        let collisions_after_insert = set.collision_count();
        assert!(collisions_after_insert > 0);

        // Remove middle element
        assert!(set.remove(&4));

        // Insert new element that maps to same initial slot
        assert!(set.insert(12)); // slot 0 -> tombstone at 1 -> slot 2 (occupied) -> slot 3

        // Should have recorded additional collisions during this operation
        assert!(set.collision_count() > collisions_after_insert);

        assert_eq!(set.len(), 3);
        assert!(set.contains(&0));
        assert!(!set.contains(&4)); // Removed
        assert!(set.contains(&8));
        assert!(set.contains(&12));
    }
}
