// SPDX-License-Identifier: Apache-2.0

use core::hash::Hash;
use core::sync::atomic::{AtomicUsize, Ordering};

use super::super::probing::{find_key_with_hash, ProbableSlot};
use super::MapTrait;

/// Represents the state of a slot in the dictionary
#[derive(Debug)]
enum Slot<K, V> {
    Occupied(K, V), // Contains a key-value pair
    Empty,          // Never used
    Tombstone,      // Previously occupied, now deleted
}

/// A dictionary implementation with linear probing for collision handling and atomic collision tracking
#[derive(Debug)]
pub struct Dictionary<K, V, const N: usize> {
    slots: [Slot<K, V>; N], // Stores key-value pairs, empty slots, or tombstones
    collision_count: AtomicUsize, // Tracks collisions atomically
}

// Entirely unstable iteration order
pub struct Iter<'a, K, V> {
    slots: core::slice::Iter<'a, Slot<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        for slot in self.slots.by_ref() {
            if let Slot::Occupied(k, v) = slot {
                return Some((k, v));
            }
        }
        None
    }
}

impl<K, V> ProbableSlot<K> for Slot<K, V>
where
    K: Eq,
{
    fn contains_key(&self, key: &K) -> bool {
        match self {
            Slot::Occupied(stored_key, _) => stored_key == key,
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

impl<K, V, const N: usize> Dictionary<K, V, N>
where
    K: Eq + Hash,
{
    /// Finds the key or an appropriate slot for insertion, returning (found, index)
    fn find_key_with_hash(&self, key: &K) -> (bool, usize) {
        find_key_with_hash(&self.slots, key, &self.collision_count)
    }

    /// Returns the total number of collisions recorded
    pub fn collision_count(&self) -> usize {
        self.collision_count.load(Ordering::Relaxed)
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            slots: self.slots.iter(),
        }
    }
}

impl<K, V, const N: usize> Default for Dictionary<K, V, N>
where
    K: Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, const N: usize> MapTrait<K, V> for Dictionary<K, V, N>
where
    K: Eq + Hash,
{
    type Iter<'a>
        = Iter<'a, K, V>
    where
        Self: 'a,
        K: 'a,
        V: 'a;
    type Keys<'a>
        = core::iter::Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a K>
    where
        Self: 'a,
        K: 'a;

    fn new() -> Self {
        Self {
            slots: core::array::from_fn(|_| Slot::Empty), // All slots start empty
            collision_count: AtomicUsize::new(0),         // Initialize to 0
        }
    }

    fn capacity(&self) -> usize {
        N
    }

    fn iter(&self) -> Self::Iter<'_> {
        self.iter()
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        let (exists, index) = self.find_key_with_hash(&key);
        if !exists {
            self.slots[index] = Slot::Occupied(key, value);
            None
        } else {
            // Key exists, replace value
            if let Slot::Occupied(_, old_value) = &mut self.slots[index] {
                Some(core::mem::replace(old_value, value))
            } else {
                unreachable!("find_key_with_hash returned true but slot is not occupied")
            }
        }
    }

    fn get(&self, key: &K) -> Option<&V> {
        let (exists, index) = self.find_key_with_hash(key);
        if exists {
            if let Slot::Occupied(_, value) = &self.slots[index] {
                Some(value)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let (exists, index) = self.find_key_with_hash(key);
        if exists {
            if let Slot::Occupied(_, value) = &mut self.slots[index] {
                Some(value)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        let (exists, index) = self.find_key_with_hash(key);
        if exists {
            let old_slot = core::mem::replace(&mut self.slots[index], Slot::Tombstone);
            if let Slot::Occupied(_, value) = old_slot {
                Some(value)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn contains_key(&self, key: &K) -> bool {
        self.find_key_with_hash(key).0
    }

    fn len(&self) -> usize {
        self.slots
            .iter()
            .filter(|s| matches!(s, Slot::Occupied(_, _)))
            .count()
    }

    fn keys(&self) -> Self::Keys<'_> {
        self.iter().map(|(k, _)| k)
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
mod test {
    use super::*;

    #[test]
    fn test_iter() {
        let mut dict = Dictionary::<_, _, 37>::new();
        dict.insert("hello", "world");
        dict.insert("foo", "bar");
        dict.insert("baz", "qux");
        let mut iter = dict.iter();
        let mut expect = [
            (false, "hello", "world"),
            (false, "foo", "bar"),
            (false, "baz", "qux"),
        ];
        for _ in 0..3 {
            let (key, value) = iter.next().unwrap();
            if let Some((found, _, _)) = expect
                .iter_mut()
                .find(|(found, ekey, eval)| !*found && ekey == key && eval == value)
            {
                *found = true;
            } else {
                panic!("Unexpected key-value pair: {:?} {:?}", key, value);
            }
        }
        assert_eq!(true, expect.iter().all(|(found, _, _)| *found));
        assert_eq!(None, iter.next());
    }
}

#[cfg(test)]
mod collision_tests {
    use super::*;

    #[test]
    fn test_new_dict_has_zero_collisions() {
        let dict: Dictionary<i32, String, 5> = Dictionary::new();
        assert_eq!(dict.collision_count(), 0);
        assert!(dict.is_empty());
        assert_eq!(dict.len(), 0);
    }

    #[test]
    fn test_basic_operations_with_collision_tracking() {
        let mut dict: Dictionary<i32, String, 10> = Dictionary::new();

        // Insert values and check collision count
        assert_eq!(dict.insert(1, "one".to_string()), None);
        assert_eq!(dict.collision_count(), 0);

        assert_eq!(dict.insert(2, "two".to_string()), None);
        let count_after_2 = dict.collision_count();

        assert_eq!(dict.insert(3, "three".to_string()), None);
        let count_after_3 = dict.collision_count();

        // Collision count should be monotonic
        assert!(count_after_3 >= count_after_2);
        assert_eq!(dict.len(), 3);
    }

    #[test]
    fn test_forced_collisions_in_small_dict() {
        let mut dict: Dictionary<i32, String, 2> = Dictionary::new();

        // With only 2 slots, we're guaranteed collisions eventually
        assert_eq!(dict.insert(1, "one".to_string()), None);
        assert_eq!(dict.collision_count(), 0);

        assert_eq!(dict.insert(2, "two".to_string()), None);
        let count_after_2 = dict.collision_count();

        // Now dict is full, remove one to make space
        assert_eq!(dict.remove(&1), Some("one".to_string()));

        assert_eq!(dict.insert(3, "three".to_string()), None);
        let count_after_3 = dict.collision_count();

        // Should have at least as many collisions as before
        assert!(count_after_3 >= count_after_2);

        assert_eq!(dict.len(), 2);
        assert_eq!(dict.get(&1), None); // Removed
        assert_eq!(dict.get(&2), Some(&"two".to_string()));
        assert_eq!(dict.get(&3), Some(&"three".to_string()));
    }

    #[test]
    fn test_collision_counting_during_lookup() {
        let mut dict: Dictionary<i32, String, 2> = Dictionary::new();

        // Fill dict completely to force future collisions
        dict.insert(1, "one".to_string());
        dict.insert(2, "two".to_string());

        let initial_collisions = dict.collision_count();

        // Multiple lookups should potentially increase collision count
        assert_eq!(dict.get(&1), Some(&"one".to_string()));
        assert_eq!(dict.get(&2), Some(&"two".to_string()));
        let after_lookup = dict.collision_count();

        // Collision count should be monotonic (not decrease)
        assert!(after_lookup >= initial_collisions);
    }

    #[test]
    fn test_collision_counting_with_tombstones() {
        let mut dict: Dictionary<i32, String, 2> = Dictionary::new();

        // Fill dict
        dict.insert(1, "one".to_string());
        dict.insert(2, "two".to_string());

        // Remove first element (creates tombstone)
        assert_eq!(dict.remove(&1), Some("one".to_string()));
        assert_eq!(dict.len(), 1);

        let collisions_after_remove = dict.collision_count();

        // Insert another value - may interact with tombstone
        assert_eq!(dict.insert(3, "three".to_string()), None);

        // Should maintain monotonic collision counting
        assert!(dict.collision_count() >= collisions_after_remove);
        assert_eq!(dict.len(), 2);
        assert_eq!(dict.get(&1), None); // Removed
        assert_eq!(dict.get(&2), Some(&"two".to_string())); // Still there
        assert_eq!(dict.get(&3), Some(&"three".to_string())); // Newly added
    }

    #[test]
    fn test_value_replacement_collision_tracking() {
        let mut dict: Dictionary<i32, String, 3> = Dictionary::new();

        dict.insert(1, "one".to_string());
        dict.insert(2, "two".to_string());
        let collisions_after_insert = dict.collision_count();

        // Replace value for existing key
        assert_eq!(dict.insert(2, "TWO".to_string()), Some("two".to_string()));

        // Collision count may increase during lookup for replacement
        assert!(dict.collision_count() >= collisions_after_insert);
        assert_eq!(dict.len(), 2); // Length unchanged
        assert_eq!(dict.get(&2), Some(&"TWO".to_string()));
    }

    #[test]
    fn test_clear_resets_collision_count() {
        let mut dict: Dictionary<i32, String, 3> = Dictionary::new();

        // Create some collisions
        dict.insert(1, "one".to_string());
        dict.insert(2, "two".to_string());
        dict.insert(3, "three".to_string());

        let _collision_count = dict.collision_count(); // May have collisions
        assert_eq!(dict.len(), 3);

        // Clear should reset everything
        dict.clear();

        assert_eq!(dict.collision_count(), 0);
        assert_eq!(dict.len(), 0);
        assert!(dict.is_empty());

        // Should work normally after clear
        assert_eq!(dict.insert(1, "new_one".to_string()), None);
        assert_eq!(dict.collision_count(), 0);
    }

    #[test]
    fn test_collision_count_increases_monotonically() {
        let mut dict: Dictionary<i32, String, 5> = Dictionary::new();
        let mut last_count = 0;

        // Insert values that will likely collide
        for i in 0..5 {
            let value = i * 5; // Values: 0, 5, 10, 15, 20
            dict.insert(value, format!("value_{}", value));

            let current_count = dict.collision_count();
            assert!(
                current_count >= last_count,
                "Collision count should not decrease: {} -> {}",
                last_count,
                current_count
            );
            last_count = current_count;
        }

        // Subsequent operations should only increase the count
        dict.get(&15); // Lookup
        assert!(dict.collision_count() >= last_count);

        dict.remove(&10); // Remove
        assert!(dict.collision_count() >= last_count);
    }

    #[test]
    fn test_collision_behavior_with_string_keys() {
        let mut dict: Dictionary<String, i32, 3> = Dictionary::new();

        // Use strings that are likely to collide in a small table
        let keys = ["a", "b", "c", "d"];

        for (i, key) in keys.iter().enumerate() {
            dict.insert(key.to_string(), i as i32);
        }

        // Should track collisions due to small table size
        let _collision_count = dict.collision_count();
        assert_eq!(dict.len(), 3); // Can only fit 3 in a size-3 table

        // Verify we can find the stored keys
        let mut found_count = 0;
        for key in keys {
            if dict.contains_key(&key.to_string()) {
                found_count += 1;
            }
        }
        assert_eq!(found_count, 3);
    }

    #[test]
    fn test_collision_counting_with_full_table() {
        let mut dict: Dictionary<i32, String, 2> = Dictionary::new();

        // Fill table completely
        assert_eq!(dict.insert(1, "one".to_string()), None);
        let count_after_first = dict.collision_count();

        assert_eq!(dict.insert(2, "two".to_string()), None);
        let count_after_second = dict.collision_count();

        // Should be monotonic
        assert!(count_after_second >= count_after_first);

        // Table is now full, create tombstone and reuse
        assert_eq!(dict.remove(&1), Some("one".to_string())); // Creates tombstone

        assert_eq!(dict.insert(3, "three".to_string()), None); // Reuses space
        let final_count = dict.collision_count();

        // Should still be monotonic
        assert!(final_count >= count_after_second);

        assert_eq!(dict.len(), 2);
        assert_eq!(dict.get(&1), None);
        assert_eq!(dict.get(&2), Some(&"two".to_string()));
        assert_eq!(dict.get(&3), Some(&"three".to_string()));
    }

    #[test]
    fn test_default_constructor_has_zero_collisions() {
        let dict: Dictionary<i32, String, 10> = Dictionary::default();
        assert_eq!(dict.collision_count(), 0);
        assert!(dict.is_empty());
    }

    #[test]
    fn test_collision_tracking_with_get_mut() {
        let mut dict: Dictionary<i32, String, 2> = Dictionary::new();

        dict.insert(1, "one".to_string());
        dict.insert(2, "two".to_string());

        let initial_collisions = dict.collision_count();

        // get_mut operations may cause collisions during lookup
        if let Some(value) = dict.get_mut(&2) {
            value.push_str("_modified");
        }

        // Should maintain monotonic collision counting
        assert!(dict.collision_count() >= initial_collisions);
        assert_eq!(dict.get(&2), Some(&"two_modified".to_string()));
    }

    #[test]
    fn test_contains_key_collision_tracking() {
        let mut dict: Dictionary<i32, String, 2> = Dictionary::new();

        dict.insert(1, "one".to_string());
        dict.insert(2, "two".to_string());

        let initial_collisions = dict.collision_count();

        // contains_key operations may cause collisions during lookup
        assert!(dict.contains_key(&1));
        assert!(dict.contains_key(&2));
        assert!(!dict.contains_key(&3));

        // Should maintain monotonic collision counting
        assert!(dict.collision_count() >= initial_collisions);
    }
}
