// SPDX-License-Identifier: Apache-2.0

//! [MapTrait] that abstracts hash maps

#[cfg(feature = "std")]
use std::collections::HashMap;

#[cfg(feature = "heapless")]
use heapless::FnvIndexMap;

pub mod staticdict;

/// Basic abstraction for a map type.
pub trait MapTrait<K, V> {
    /// Iterator type for key-value pairs
    type Iter<'a>: Iterator<Item = (&'a K, &'a V)>
    where
        Self: 'a,
        K: 'a,
        V: 'a;
    /// Iterator type for keys
    type Keys<'a>: Iterator<Item = &'a K>
    where
        Self: 'a,
        K: 'a;

    /// Creates an empty map
    fn new() -> Self
    where
        Self: Sized;
    /// Returns the number of elements the map can hold
    fn capacity(&self) -> usize;
    /// Inserts a key-value pair into the map.
    /// If the map did not have this key present, None is returned.
    fn insert(&mut self, key: K, value: V) -> Option<V>;
    /// Return an iterator over the key-value pairs of the map.
    fn iter(&self) -> Self::Iter<'_>;
    /// Returns a reference to the value corresponding to the key.
    fn get(&self, key: &K) -> Option<&V>;
    /// Returns a reference to the value corresponding to the key.
    fn get_mut(&mut self, key: &K) -> Option<&mut V>;
    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    fn remove(&mut self, key: &K) -> Option<V>;
    /// Returns true if the map contains a value for the specified key.
    fn contains_key(&self, key: &K) -> bool;
    /// Returns the number of elements in the map.
    fn len(&self) -> usize;
    /// Returns an iterator over the keys of the map.
    fn keys(&self) -> Self::Keys<'_>;
    /// Returns true if the map contains no elements.
    fn is_empty(&self) -> bool;
    /// Returns true if the map is full.
    fn is_full(&self) -> bool {
        false
    }
    /// Clear the map
    fn clear(&mut self);
}

#[cfg(feature = "std")]
impl<K, V> MapTrait<K, V> for std::collections::HashMap<K, V>
where
    K: std::cmp::Eq + std::hash::Hash,
{
    type Iter<'a>
        = std::collections::hash_map::Iter<'a, K, V>
    where
        Self: 'a,
        K: 'a,
        V: 'a;
    type Keys<'a>
        = std::collections::hash_map::Keys<'a, K, V>
    where
        Self: 'a,
        K: 'a;

    fn capacity(&self) -> usize {
        HashMap::capacity(self)
    }
    fn new() -> Self {
        HashMap::new()
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        HashMap::insert(self, key, value)
    }

    fn iter(&self) -> Self::Iter<'_> {
        HashMap::iter(self)
    }

    fn get(&self, key: &K) -> Option<&V> {
        HashMap::get(self, key)
    }
    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        HashMap::get_mut(self, key)
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        HashMap::remove(self, key)
    }

    fn contains_key(&self, key: &K) -> bool {
        HashMap::contains_key(self, key)
    }

    fn len(&self) -> usize {
        HashMap::len(self)
    }
    fn keys(&self) -> Self::Keys<'_> {
        HashMap::keys(self)
    }

    fn is_empty(&self) -> bool {
        HashMap::is_empty(self)
    }
    fn clear(&mut self) {
        self.clear()
    }
}

#[cfg(feature = "heapless")]
impl<K, V, const N: usize> MapTrait<K, V> for heapless::FnvIndexMap<K, V, N>
where
    K: Eq + core::hash::Hash,
{
    type Iter<'a>
        = heapless::IndexMapIter<'a, K, V>
    where
        Self: 'a,
        K: 'a,
        V: 'a;
    type Keys<'a>
        = heapless::IndexMapKeys<'a, K, V>
    where
        Self: 'a,
        K: 'a;

    fn new() -> Self {
        FnvIndexMap::new()
    }

    fn capacity(&self) -> usize {
        FnvIndexMap::capacity(self)
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        FnvIndexMap::insert(self, key, value).ok().flatten()
    }

    fn iter(&self) -> Self::Iter<'_> {
        FnvIndexMap::iter(self)
    }

    fn get(&self, key: &K) -> Option<&V> {
        FnvIndexMap::get(self, key)
    }
    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        FnvIndexMap::get_mut(self, key)
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        FnvIndexMap::remove(self, key)
    }

    fn contains_key(&self, key: &K) -> bool {
        FnvIndexMap::contains_key(self, key)
    }

    fn len(&self) -> usize {
        FnvIndexMap::len(self)
    }
    fn keys(&self) -> Self::Keys<'_> {
        FnvIndexMap::keys(self)
    }

    fn is_empty(&self) -> bool {
        FnvIndexMap::is_empty(self)
    }
    fn clear(&mut self) {
        self.clear()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_maps<M: MapTrait<u32, u32>>(map: &mut M) {
        assert_eq!(map.insert(1, 2), None);
        assert_eq!(map.insert(1, 3), Some(2));
        assert_eq!(map.get(&1), Some(&3));
        assert_eq!(map.get(&2), None);
        assert_eq!(map.remove(&1), Some(3));
        assert_eq!(map.get(&1), None);
        map.clear();
        assert_eq!(map.is_empty(), true);
    }
    // Test basic iteration, ignoring ordering
    fn test_map_iter<M: MapTrait<u32, u32>>(map: &mut M) {
        map.clear();
        assert_eq!(map.insert(1, 20), None);
        assert_eq!(map.insert(2, 30), None);
        assert_eq!(map.insert(3, 40), None);
        let mut expect = [(false, 1, 20), (false, 2, 30), (false, 3, 40)];
        let mut iter = map.iter();
        for _ in 0..3 {
            let (_key, value) = iter.next().unwrap();
            if let Some((found, _, _)) = expect
                .iter_mut()
                .find(|(found, key, val)| !*found && key == key && val == value)
            {
                *found = true;
            }
        }
        assert_eq!(true, expect.iter().all(|(found, _, _)| *found));
        assert_eq!(None, iter.next());
    }

    #[test]
    fn basic_test() {
        let mut map = staticdict::Dictionary::<u32, u32, 16>::new();
        test_maps(&mut map);
        test_map_iter(&mut map);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn heapless_test() {
        let mut map = heapless::FnvIndexMap::<u32, u32, 16>::new();
        test_maps(&mut map);
        test_map_iter(&mut map);
    }

    #[cfg(feature = "std")]
    #[test]
    fn std_test() {
        let mut map = std::collections::HashMap::<u32, u32>::new();
        test_maps(&mut map);
        test_map_iter(&mut map);
    }
}
