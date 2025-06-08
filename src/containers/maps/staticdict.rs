// SPDX-License-Identifier: Apache-2.0

use core::hash::Hash;

use super::super::probing::{find_key_with_hash, ProbableSlot};
use super::MapTrait;

/// Represents the state of a slot in the dictionary
#[derive(Debug)]
enum Slot<K, V> {
    Occupied(K, V), // Contains a key-value pair
    Empty,          // Never used
    Tombstone,      // Previously occupied, now deleted
}

/// A fixed-capacity hash map implementation with linear probing for collision handling
///
/// This dictionary provides O(1) average case insert, remove, and lookup operations
/// using open addressing with linear probing. It uses tombstones to handle
/// deletions efficiently while maintaining probe sequences.
///
/// The dictionary has a fixed capacity `N` determined at compile time and does not
/// allocate memory at runtime, making it suitable for no-std environments.
#[derive(Debug)]
pub struct Dictionary<K, V, const N: usize> {
    slots: [Slot<K, V>; N], // Stores key-value pairs, empty slots, or tombstones
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
        find_key_with_hash(&self.slots, key)
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
mod collision_behavior_tests {
    use super::*;

    #[test]
    fn test_basic_operations_in_small_dict() {
        let mut dict: Dictionary<i32, &'static str, 10> = Dictionary::new();

        // Insert values that may collide
        assert_eq!(dict.insert(1, "one"), None);
        assert_eq!(dict.insert(2, "two"), None);
        assert_eq!(dict.insert(3, "three"), None);

        assert_eq!(dict.len(), 3);

        // Verify all values are findable
        assert_eq!(dict.get(&1), Some(&"one"));
        assert_eq!(dict.get(&2), Some(&"two"));
        assert_eq!(dict.get(&3), Some(&"three"));
    }

    #[test]
    fn test_forced_collisions_in_small_dict() {
        let mut dict: Dictionary<i32, &'static str, 2> = Dictionary::new();

        // With only 2 slots, we're guaranteed collisions eventually
        assert_eq!(dict.insert(1, "one"), None);
        assert_eq!(dict.insert(2, "two"), None);

        // Now dict is full, remove one to make space
        assert_eq!(dict.remove(&1), Some("one"));

        assert_eq!(dict.insert(3, "three"), None);

        assert_eq!(dict.len(), 2);
        assert_eq!(dict.get(&1), None); // Removed
        assert_eq!(dict.get(&2), Some(&"two"));
        assert_eq!(dict.get(&3), Some(&"three"));
    }

    #[test]
    fn test_lookup_with_potential_collisions() {
        let mut dict: Dictionary<i32, &'static str, 2> = Dictionary::new();

        // Fill dict completely to force collisions
        dict.insert(1, "one");
        dict.insert(2, "two");

        // Multiple lookups should work correctly despite collisions
        assert_eq!(dict.get(&1), Some(&"one"));
        assert_eq!(dict.get(&2), Some(&"two"));
        assert_eq!(dict.get(&3), None);
    }

    #[test]
    fn test_tombstone_handling() {
        let mut dict: Dictionary<i32, &'static str, 2> = Dictionary::new();

        // Fill dict
        dict.insert(1, "one");
        dict.insert(2, "two");

        // Remove first element (creates tombstone)
        assert_eq!(dict.remove(&1), Some("one"));
        assert_eq!(dict.len(), 1);

        // Insert another value - should properly handle tombstone
        assert_eq!(dict.insert(3, "three"), None);

        assert_eq!(dict.len(), 2);
        assert_eq!(dict.get(&1), None); // Removed
        assert_eq!(dict.get(&2), Some(&"two")); // Still there
        assert_eq!(dict.get(&3), Some(&"three")); // Newly added
    }

    #[test]
    fn test_value_replacement() {
        let mut dict: Dictionary<i32, &'static str, 3> = Dictionary::new();

        dict.insert(1, "one");
        dict.insert(2, "two");

        // Replace value for existing key
        assert_eq!(dict.insert(2, "TWO"), Some("two"));

        assert_eq!(dict.len(), 2); // Length unchanged
        assert_eq!(dict.get(&1), Some(&"one"));
        assert_eq!(dict.get(&2), Some(&"TWO"));
    }

    #[test]
    fn test_clear_functionality() {
        let mut dict: Dictionary<i32, &'static str, 3> = Dictionary::new();

        // Create some entries that may collide
        dict.insert(1, "one");
        dict.insert(2, "two");
        dict.insert(3, "three");

        assert_eq!(dict.len(), 3);

        // Clear should reset everything
        dict.clear();

        assert_eq!(dict.len(), 0);
        assert!(dict.is_empty());

        // Should work normally after clear
        assert_eq!(dict.insert(1, "new_one"), None);
        assert_eq!(dict.len(), 1);
        assert_eq!(dict.get(&1), Some(&"new_one"));
    }

    #[test]
    fn test_operations_with_potential_collisions() {
        let mut dict: Dictionary<i32, &'static str, 5> = Dictionary::new();

        // Insert values that will likely collide
        let values = ["value_0", "value_5", "value_10", "value_15", "value_20"];
        for (i, &value_str) in values.iter().enumerate() {
            let value = (i * 5) as i32; // Values: 0, 5, 10, 15, 20
            dict.insert(value, value_str);
        }

        assert_eq!(dict.len(), 5);

        // All values should be findable
        for (i, &expected_str) in values.iter().enumerate() {
            let key = (i * 5) as i32;
            assert_eq!(dict.get(&key), Some(&expected_str));
        }

        // Remove some values
        assert_eq!(dict.remove(&10), Some("value_10"));
        assert_eq!(dict.len(), 4);
        assert_eq!(dict.get(&10), None);

        // Other values should still be findable
        assert_eq!(dict.get(&0), Some(&"value_0"));
        assert_eq!(dict.get(&5), Some(&"value_5"));
        assert_eq!(dict.get(&15), Some(&"value_15"));
        assert_eq!(dict.get(&20), Some(&"value_20"));
    }

    #[test]
    fn test_string_keys_in_small_table() {
        let mut dict: Dictionary<&'static str, i32, 3> = Dictionary::new();

        // Use strings that are likely to collide in a small table
        let keys = ["a", "b", "c", "d"];

        for (i, &key) in keys.iter().enumerate() {
            dict.insert(key, i as i32);
        }

        assert_eq!(dict.len(), 3); // Can only fit 3 in a size-3 table

        // Verify we can find the stored keys
        let mut found_count = 0;
        for &key in &keys {
            if dict.contains_key(&key) {
                found_count += 1;
            }
        }
        assert_eq!(found_count, 3);
    }

    #[test]
    fn test_full_table_operations() {
        let mut dict: Dictionary<i32, &'static str, 2> = Dictionary::new();

        // Fill table completely
        assert_eq!(dict.insert(1, "one"), None);
        assert_eq!(dict.insert(2, "two"), None);

        // Table is now full, create tombstone and reuse
        assert_eq!(dict.remove(&1), Some("one")); // Creates tombstone
        assert_eq!(dict.insert(3, "three"), None); // Reuses space

        assert_eq!(dict.len(), 2);
        assert_eq!(dict.get(&1), None);
        assert_eq!(dict.get(&2), Some(&"two"));
        assert_eq!(dict.get(&3), Some(&"three"));
    }

    #[test]
    fn test_default_constructor() {
        let dict: Dictionary<i32, &'static str, 10> = Dictionary::default();
        assert!(dict.is_empty());
        assert_eq!(dict.len(), 0);
    }

    #[test]
    fn test_get_mut_functionality() {
        let mut dict: Dictionary<i32, &'static str, 2> = Dictionary::new();

        dict.insert(1, "one");
        dict.insert(2, "two");

        // get_mut operations should work correctly with collisions
        if let Some(value) = dict.get_mut(&2) {
            *value = "two_modified";
        }

        assert_eq!(dict.get(&1), Some(&"one"));
        assert_eq!(dict.get(&2), Some(&"two_modified"));
    }

    #[test]
    fn test_contains_key_functionality() {
        let mut dict: Dictionary<i32, &'static str, 2> = Dictionary::new();

        dict.insert(1, "one");
        dict.insert(2, "two");

        // contains_key operations should work correctly with collisions
        assert!(dict.contains_key(&1));
        assert!(dict.contains_key(&2));
        assert!(!dict.contains_key(&3));
    }
}
