// SPDX-License-Identifier: Apache-2.0

use core::hash::{Hash, Hasher};

use super::MapTrait;

use super::super::djb2hash::Djb2Hasher;

/// A minimal statically sized dictionary, no collision handling
pub struct Dictionary<K, V, const N: usize> {
    items: [Option<(K, V)>; N],
}

// Entirely unstable iteration order
pub struct Iter<'a, K, V> {
    items: core::slice::Iter<'a, Option<(K, V)>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((k, v)) = self.items.by_ref().flatten().next() {
            return Some((k, v));
        }
        None
    }
}

impl<K, V, const N: usize> Dictionary<K, V, N>
where
    K: Eq + Hash,
{
    fn hash_key(&self, key: &K) -> usize {
        let mut hasher = Djb2Hasher::default();
        key.hash(&mut hasher);
        hasher.finish() as usize % N
    }

    fn find_key_with_hash(&self, key: &K) -> (bool, usize) {
        let hash = self.hash_key(key);
        if let Some((ref stored_key, _)) = &self.items[hash] {
            (stored_key == key, hash)
        } else {
            (false, hash)
        }
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            items: self.items.iter(),
        }
    }
}

impl<K, V, const N: usize> MapTrait<K, V> for Dictionary<K, V, N>
where
    K: Eq + Hash,
{
    type Iter<'a> = Iter<'a, K, V>  where Self: 'a, K: 'a, V: 'a;
    type Keys<'a> = core::iter::Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a K> where Self: 'a, K: 'a;

    fn new() -> Self {
        Self {
            items: core::array::from_fn(|_| None),
        }
    }

    fn iter(&self) -> Self::Iter<'_> {
        self.iter()
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        let (exists, hash) = self.find_key_with_hash(&key);
        if !exists {
            self.items[hash] = Some((key, value));
            None
        } else {
            self.items[hash]
                .as_mut()
                .map(|(_, old_value)| core::mem::replace(old_value, value))
        }
    }

    fn get(&self, key: &K) -> Option<&V> {
        let (exists, hash) = self.find_key_with_hash(key);
        exists
            .then(|| &self.items[hash])
            .and_then(|item| item.as_ref().map(|(_, v)| v))
    }

    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let (exists, hash) = self.find_key_with_hash(key);
        exists
            .then(|| &mut self.items[hash])
            .and_then(|item| item.as_mut().map(|(_, v)| v))
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        let (exists, hash) = self.find_key_with_hash(key);
        exists
            .then(|| self.items[hash].take())
            .and_then(|item| item.map(|(_, v)| v))
    }

    fn contains_key(&self, key: &K) -> bool {
        self.find_key_with_hash(key).0
    }

    fn len(&self) -> usize {
        self.items.iter().filter(|item| item.is_some()).count()
    }
    fn keys(&self) -> Self::Keys<'_> {
        self.iter().map(|(k, _)| k)
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn clear(&mut self) {
        self.items.fill_with(|| None);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_iter() {
        let mut dict = super::Dictionary::<_, _, 37>::new();
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
                .find(|(found, key, val)| !*found && key == key && val == value)
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
