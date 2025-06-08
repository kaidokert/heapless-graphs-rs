// SPDX-License-Identifier: Apache-2.0

use core::hash::Hash;

use super::SetTrait;
use crate::containers::probing::{find_key_with_hash, ProbableSlot};

/// Represents the state of a slot in the set
#[derive(Debug)]
enum Slot<K> {
    Occupied(K), // Contains a key
    Empty,       // Never used
    Tombstone,   // Previously occupied, now deleted
}

/// A fixed-capacity hash set implementation with linear probing for collision handling
///
/// This set provides O(1) average case insert, remove, and lookup operations
/// using open addressing with linear probing. It uses tombstones to handle
/// deletions efficiently while maintaining probe sequences.
///
/// The set has a fixed capacity `N` determined at compile time and does not
/// allocate memory at runtime, making it suitable for no-std environments.
#[derive(Debug)]
pub struct Set<K, const N: usize> {
    slots: [Slot<K>; N], // Stores keys, empty slots, or tombstones
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
        find_key_with_hash(&self.slots, key)
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
        }
    }

    fn insert(&mut self, key: K) -> bool {
        let (exists, index) = self.find_key_with_hash(&key);
        if !exists {
            self.slots[index] = Slot::Occupied(key);
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
    }
}

#[cfg(test)]
mod collision_behavior_tests {
    use super::*;

    #[test]
    fn test_basic_operations_in_small_table() {
        let mut set: Set<i32, 10> = Set::new();

        // Insert values that may collide
        assert!(set.insert(0));
        assert!(set.insert(10));
        assert!(set.insert(20));
        assert_eq!(set.len(), 3);

        // Verify all values are findable
        assert!(set.contains(&0));
        assert!(set.contains(&10));
        assert!(set.contains(&20));
    }

    #[test]
    fn test_forced_collisions_in_small_table() {
        let mut set: Set<i32, 2> = Set::new();

        // With only 2 slots, we're guaranteed collisions eventually
        assert!(set.insert(1));
        assert!(set.insert(2));

        // Now table is full, remove one to make space
        assert!(set.remove(&1));

        assert!(set.insert(3)); // This insertion will handle collisions

        assert_eq!(set.len(), 2);
        assert!(!set.contains(&1)); // Removed
        assert!(set.contains(&2));
        assert!(set.contains(&3));
    }

    #[test]
    fn test_lookup_with_potential_collisions() {
        let mut set: Set<i32, 2> = Set::new();

        // Fill table completely to force collisions
        set.insert(1);
        set.insert(2);

        // Multiple lookups should work correctly despite collisions
        assert!(set.contains(&1));
        assert!(set.contains(&2));
        assert!(!set.contains(&3));
    }

    #[test]
    fn test_tombstone_handling() {
        let mut set: Set<i32, 2> = Set::new();

        // Fill table
        set.insert(1);
        set.insert(2);

        // Remove first element (creates tombstone)
        assert!(set.remove(&1));
        assert_eq!(set.len(), 1);

        // Insert another value - should properly handle tombstone
        assert!(set.insert(3));

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

        // Try to insert 2 again (duplicate)
        assert!(!set.insert(2)); // Should return false (not inserted)

        assert_eq!(set.len(), 2); // Length unchanged
        assert!(set.contains(&1));
        assert!(set.contains(&2));
    }

    #[test]
    fn test_clear_functionality() {
        let mut set: Set<i32, 3> = Set::new();

        // Create some entries that may collide
        set.insert(0);
        set.insert(3);
        set.insert(6);

        assert_eq!(set.len(), 3);

        // Clear should reset everything
        set.clear();

        assert_eq!(set.len(), 0);
        assert!(set.is_empty());

        // Should work normally after clear
        assert!(set.insert(1));
        assert_eq!(set.len(), 1);
        assert!(set.contains(&1));
    }

    #[test]
    fn test_operations_with_potential_collisions() {
        let mut set: Set<i32, 5> = Set::new();

        // Insert values that will likely collide
        for i in 0..5 {
            let value = i * 5; // Values: 0, 5, 10, 15, 20
            set.insert(value);
        }

        assert_eq!(set.len(), 5);

        // All values should be findable
        for i in 0..5 {
            let value = i * 5;
            assert!(set.contains(&value));
        }

        // Remove some values
        assert!(set.remove(&10));
        assert_eq!(set.len(), 4);
        assert!(!set.contains(&10));

        // Other values should still be findable
        assert!(set.contains(&0));
        assert!(set.contains(&5));
        assert!(set.contains(&15));
        assert!(set.contains(&20));
    }

    #[test]
    fn test_string_keys_in_small_table() {
        let mut set: Set<&'static str, 3> = Set::new();

        // Use strings that are likely to collide in a small table
        let keys = ["a", "b", "c", "d"];

        for &key in &keys {
            set.insert(key);
        }

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
    fn test_full_table_operations() {
        let mut set: Set<i32, 2> = Set::new();

        // Fill table completely
        assert!(set.insert(1));
        assert!(set.insert(2));

        // Table is now full, create tombstone and reuse
        assert!(set.remove(&1)); // Creates tombstone
        assert!(set.insert(3)); // Reuses space

        assert_eq!(set.len(), 2);
        assert!(!set.contains(&1));
        assert!(set.contains(&2));
        assert!(set.contains(&3));
    }

    #[test]
    fn test_default_constructor() {
        let set: Set<i32, 10> = Set::default();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_remove_patterns_with_collisions() {
        let mut set: Set<i32, 4> = Set::new();

        // Insert a sequence that creates collisions
        set.insert(0); // slot 0
        set.insert(4); // likely collision
        set.insert(8); // likely collision

        // Remove middle element
        assert!(set.remove(&4));

        // Insert new element that maps to same initial slot
        assert!(set.insert(12));

        assert_eq!(set.len(), 3);
        assert!(set.contains(&0));
        assert!(!set.contains(&4)); // Removed
        assert!(set.contains(&8));
        assert!(set.contains(&12));
    }
}
