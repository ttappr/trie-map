//! A trie whose keys can be any string with no restrictions on characters.
//! This is achieved by base 16 encoding the key as it's inserted into the trie.
//! 

use std::borrow::Borrow;

use crate::TrieMap;

/// A trie whose keys can be any string with no restrictions on characters.
/// This is achieved by base 16 encoding the key as it's inserted into the trie.
/// The encoding is done via an iterator that only encodes the number of bytes
/// needed to determine if a key is missing or present. So determining a miss
/// is as fast as possible for operations such as `contains()`.
/// 
/// Each node has a fixed-size array 16 successors. And a value of any type
/// can be inserted with a key. The values are stored in independent contiguous
/// memory, while the terminal trie nodes hold handles to their values.
/// 
pub struct TrieMapBase16<V> {
    trie: TrieMap<V, 16, b'a'>,
}

impl<V> TrieMapBase16<V> { 
    /// Creates an empty `TrieMapBase16`.
    /// 
    pub fn new() -> Self {
        Self { trie: TrieMap::new() }
    }

    /// Returns `true` if the map contains a value for the specified key.
    /// 
    pub fn contains(&self, key: &str) -> bool {
        self.trie.get_by_iter(Encoder::new(key.bytes())).is_some()
    }

    /// Returns a reference to the value corresponding to the key, or `None` if
    /// the key is not present in the map.
    /// ```
    /// use trie_map::trie_map_base16::TrieMapBase16;
    /// 
    /// let mut trie = TrieMapBase16::new();
    /// 
    /// trie.insert("👋", 1);
    /// trie.insert("🌍", 2);
    /// 
    /// assert_eq!(trie.get("👋"), Some(&1));
    /// assert_eq!(trie.get("🌍"), Some(&2));
    /// 
    /// ````
    pub fn get(&self, key: &str) -> Option<&V> {
        self.trie.get_by_iter(Encoder::new(key.bytes()))
    }

    /// Returns a mutable reference to the value corresponding to the key, or
    /// `None` if the key is not present in the map.
    /// 
    pub fn get_mut(&mut self, key: &str) -> Option<&mut V> {
        self.trie.get_mut_by_iter(Encoder::new(key.bytes()))
    }

    /// If the key-value pair is not present in the map, inserts it and returns
    /// a mutable reference to the value. If the key-value pair is present,
    /// returns a mutable reference to the already present value.
    /// 
    pub fn get_or_insert<K>(&mut self, key: K, value: V) -> &mut V 
    where
        K: Borrow<str>,
    {
        let iter = Encoder::new(key.borrow().bytes());
        self.trie.get_or_insert_by_iter(iter, value)
    }

    /// If the key-value pair is not present in the map, inserts it and returns
    /// a mutable reference to the value. If the key-value pair is present,
    /// returns a mutable reference to the already present value.
    /// 
    pub fn get_or_insert_with<K, F>(&mut self, key: K, f: F) -> &mut V 
    where
        K: Borrow<str>,
        F: FnOnce() -> V,
    {
        let iter = Encoder::new(key.borrow().bytes());
        self.trie.get_or_insert_by_iter_with(iter, f)
    }

    /// Inserts a key-value pair into the map. If the key already had a value
    /// present in the map, that value is returned. Otherwise `None` is
    /// returned.
    /// 
    pub fn insert<K>(&mut self, key: K, value: V) -> Option<V> 
    where
        K: Borrow<str>,
    {
        let iter = Encoder::new(key.borrow().bytes());
        self.trie.insert_by_iter(iter, value)
    }

    /// Returns an iterator over the key-value pairs of the map in canonical
    /// order.
    /// 
    pub fn iter(&self) -> Iter<V> {
        self.into_iter()
    }

    /// Returns an iterator over the key-value pairs of the map. The values
    /// are mutable.
    /// 
    pub fn iter_mut(&mut self) -> IterMut<V> {
        self.into_iter()
    }

    /// Returns an iterator over the keys of the map in canonical order.
    /// 
    pub fn keys(&self) -> Keys<V> {
        Keys::new(self.trie.keys())
    }

    /// Returns the number of key-value pairs in the map.
    /// 
    pub fn len(&self) -> usize {
        self.trie.len()
    }

    /// Returns `true` if the map contains no key-value pairs.
    /// 
    pub fn is_empty(&self) -> bool {
        self.trie.is_empty()
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map. If the key was not present in the map,
    /// `None` is returned.
    /// 
    pub fn remove(&mut self, key: &str) -> Option<V> {
        self.trie.remove_by_iter(Encoder::new(key.bytes()))
    }

    /// Returns an iterator over the values of the map. They will be in the 
    /// same order as the keys.
    /// 
    pub fn values(&self) -> Values<V> {
        Values::new(self.trie.values())
    }

    /// Removes all key-value pairs from the map.
    /// 
    pub fn clear(&mut self) {
        self.trie.clear();
    }
}

/// Internal iterator that encodes the key as it's iterated over.
/// 
struct Encoder<K> {
    key: K,
    buf: u8,
}
impl<K> Encoder<K> 
where
    K: Iterator<Item=u8>,
{
    fn new(iter: K) -> Self {
        Self { key: iter, buf: 0 }
    }
}

impl<K> Iterator for Encoder<K> 
where
    K: Iterator<Item=u8>,
{
    type Item = u8;

    /// Progressively Base16 encodes the key as it advances during iteration.
    /// 
    fn next(&mut self) -> Option<Self::Item> {
        if self.buf > 0 {
            let b = self.buf;
            self.buf = 0;
            Some(b + b'a')
        } else if let Some(b) = self.key.next() {
            self.buf = b & 0x0f;
            let b = b >> 4;
            Some(b + b'a')
        } else {
            None
        }
    }
}

/// Decodes a Base16 encoded string into a `String`.
/// 
fn decode(bytes: &[u8]) -> String {
    let mut str = Vec::new();
    let mut buf = 0;
    for (i, b) in bytes.iter().copied().enumerate() {
        if i & 1 == 0 {
            buf = (b - b'a') << 4;
        } else {
            buf |= b - b'a';
            str.push(buf);
        }
    }
    unsafe {
        String::from_utf8_unchecked(str)
    }
}

pub struct IntoIter<V> {
    iter: crate::iterators::IntoIter<V, 16, b'a'>,
}

impl<V> Iterator for IntoIter<V> {
    type Item = (String, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (decode(&k), v))
    }
}

impl<V> DoubleEndedIterator for IntoIter<V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, v)| (decode(&k), v))
    }
}

impl<V> IntoIterator for TrieMapBase16<V> {
    type Item = (String, V);
    type IntoIter = IntoIter<V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { iter: self.trie.into_iter() }
    }
}

pub struct Iter<'a, V> {
    iter: crate::iterators::Iter<'a, V, 16, b'a'>,
}

impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (String, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (decode(&k), v))
    }
}

impl<'a, V> DoubleEndedIterator for Iter<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, v)| (decode(&k), v))
    }
}

impl<'a, V> IntoIterator for &'a TrieMapBase16<V> {
    type Item = (String, &'a V);
    type IntoIter = Iter<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        Iter { iter: (&self.trie).into_iter() }
    }
}

pub struct IterMut<'a, V> {
    iter: crate::iterators::IterMut<'a, V, 16, b'a'>,
}

impl<'a, V> Iterator for IterMut<'a, V> {
    type Item = (String, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (decode(&k), v))
    }
}

impl<'a, V> DoubleEndedIterator for IterMut<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, v)| (decode(&k), v))
    }
}

impl<'a, V> IntoIterator for &'a mut TrieMapBase16<V> {
    type Item = (String, &'a mut V);
    type IntoIter = IterMut<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut { iter: (&mut self.trie).into_iter() }
    }
}

pub struct Keys<'a, V> {
    iter: crate::iterators::Keys<'a, V, 16, b'a'>,
}

impl<'a, V> Keys<'a, V> {
    fn new(iter: crate::iterators::Keys<'a, V, 16, b'a'>) -> Self {
        Self { iter  }
    }
}

impl<'a, V> Iterator for Keys<'a, V> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|k| decode(&k))
    }
}

impl<'a, V> DoubleEndedIterator for Keys<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|k| decode(&k))
    }
}

pub struct Values<'a, V> {
    iter: crate::iterators::Values<'a, V, 16, b'a'>,
}

impl<'a, V> Values<'a, V> {
    fn new(iter: crate::iterators::Values<'a, V, 16, b'a'>) -> Self {
        Self { iter  }
    }
}

impl<'a, V> Iterator for Values<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, V> DoubleEndedIterator for Values<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert() {
        let mut trie = TrieMapBase16::new();
        assert_eq!(trie.insert("hello", 1), None);
        assert_eq!(trie.insert("hello", 2), Some(1));
        assert_eq!(trie.insert("world", 3), None);
        assert_eq!(trie.insert("world", 4), Some(3));
        assert_eq!(trie.insert("hello", 5), Some(2));
        assert_eq!(trie.insert("world", 6), Some(4));

        assert_eq!(trie.insert("Γειά σου", 1), None);
        assert_eq!(trie.insert("Γειά σου", 2), Some(1));
        assert_eq!(trie.insert("Κόσμε", 3), None);
        assert_eq!(trie.insert("Κόσμε", 4), Some(3));
        assert_eq!(trie.insert("Γειά σου", 5), Some(2));
        assert_eq!(trie.insert("Κόσμε", 6), Some(4));
    }

    #[test]
    fn get() {
        let mut trie = TrieMapBase16::new();
        assert_eq!(trie.get("hello"), None);
        assert_eq!(trie.insert("hello", 1), None);
        assert_eq!(trie.get("hello"), Some(&1));
        assert_eq!(trie.get("world"), None);
        assert_eq!(trie.insert("world", 2), None);
        assert_eq!(trie.get("world"), Some(&2));
        assert_eq!(trie.get("hello"), Some(&1));

        assert_eq!(trie.get("こんにちは"), None);
        assert_eq!(trie.insert("こんにちは", 3), None);
        assert_eq!(trie.get("こんにちは"), Some(&3));
        assert_eq!(trie.get("世界"), None);
        assert_eq!(trie.insert("世界", 4), None);
        assert_eq!(trie.get("世界"), Some(&4));
        assert_eq!(trie.get("こんにちは"), Some(&3));

        trie.insert("👋", 42);
        trie.insert("🌍", 43);

        assert_eq!(trie.get("👋"), Some(&42));
        assert_eq!(trie.get("🌍"), Some(&43));
    }

    #[test]
    fn get_mut() {
        let mut trie = TrieMapBase16::new();
        assert_eq!(trie.get_mut("hello"), None);
        assert_eq!(trie.insert("hello", 1), None);
        assert_eq!(trie.get_mut("hello"), Some(&mut 1));
        assert_eq!(trie.get_mut("world"), None);
        assert_eq!(trie.insert("world", 2), None);
        assert_eq!(trie.get_mut("world"), Some(&mut 2));
        assert_eq!(trie.get_mut("hello"), Some(&mut 1));
    }

    #[test]
    fn get_or_insert() {
        let mut trie = TrieMapBase16::new();
        assert_eq!(trie.get_or_insert("hello", 1), &mut 1);
        assert_eq!(trie.get_or_insert("hello", 2), &mut 1);
        assert_eq!(trie.get_or_insert("world", 3), &mut 3);
        assert_eq!(trie.get_or_insert("world", 4), &mut 3);
        assert_eq!(trie.get_or_insert("hello", 5), &mut 1);
        assert_eq!(trie.get_or_insert("world", 6), &mut 3);

        assert_eq!(trie.get_or_insert("こんにちは", 1), &mut 1);
        assert_eq!(trie.get_or_insert("こんにちは", 2), &mut 1);
        assert_eq!(trie.get_or_insert("世界", 3), &mut 3);
        assert_eq!(trie.get_or_insert("世界", 4), &mut 3);
        assert_eq!(trie.get_or_insert("こんにちは", 5), &mut 1);
        assert_eq!(trie.get_or_insert("世界", 6), &mut 3);

        *trie.get_or_insert("こんにちは", 0) = 99;
        assert_eq!(trie.get_or_insert("こんにちは", 0), &mut 99);
    }

    #[test]
    fn contains() {
        let mut trie = TrieMapBase16::new();
        assert_eq!(trie.contains("hello"), false);
        assert_eq!(trie.insert("hello", 1), None);
        assert_eq!(trie.contains("hello"), true);
        assert_eq!(trie.contains("world"), false);
        assert_eq!(trie.insert("world", 2), None);
        assert_eq!(trie.contains("world"), true);
        assert_eq!(trie.contains("hello"), true);
    }

    #[test]
    fn remove() {
        let mut trie = TrieMapBase16::new();
        assert_eq!(trie.remove("hello"), None);
        assert_eq!(trie.insert("hello", 1), None);
        assert_eq!(trie.remove("hello"), Some(1));
        assert_eq!(trie.remove("hello"), None);
    }

    #[test]
    fn iter() {
        let mut trie = TrieMapBase16::new();
        trie.insert("hello", 1);
        trie.insert("world", 2);
        trie.insert("こんにちは", 3);
        trie.insert("世界", 4);

        let mut iter = trie.into_iter();
        assert_eq!(iter.next(), Some(("hello".to_string(), 1)));
        assert_eq!(iter.next(), Some(("world".to_string(), 2)));
        assert_eq!(iter.next(), Some(("こんにちは".to_string(), 3)));
        assert_eq!(iter.next(), Some(("世界".to_string(), 4)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut trie = TrieMapBase16::new();
        trie.insert("hello", 1);
        trie.insert("world", 2);
        trie.insert("こんにちは", 3);
        trie.insert("世界", 4);

        let mut iter = trie.iter_mut();
        assert_eq!(iter.next(), Some(("hello".to_string(), &mut 1)));
        assert_eq!(iter.next(), Some(("world".to_string(), &mut 2)));
        assert_eq!(iter.next(), Some(("こんにちは".to_string(), &mut 3)));
        assert_eq!(iter.next(), Some(("世界".to_string(), &mut 4)));
        assert_eq!(iter.next(), None);

        for (_, v) in &mut trie {
            *v += 1;
        }
        let mut iter = trie.iter_mut();
        assert_eq!(iter.next(), Some(("hello".to_string(), &mut 2)));
        assert_eq!(iter.next(), Some(("world".to_string(), &mut 3)));
        assert_eq!(iter.next(), Some(("こんにちは".to_string(), &mut 4)));
        assert_eq!(iter.next(), Some(("世界".to_string(), &mut 5)));
        assert_eq!(iter.next(), None);

        let mut iter = trie.iter_mut().rev();
        assert_eq!(iter.next(), Some(("世界".to_string(), &mut 5)));
        assert_eq!(iter.next(), Some(("こんにちは".to_string(), &mut 4)));
        assert_eq!(iter.next(), Some(("world".to_string(), &mut 3)));
        assert_eq!(iter.next(), Some(("hello".to_string(), &mut 2)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn keys() {
        let mut trie = TrieMapBase16::new();
        trie.insert("hello", 1);
        trie.insert("world", 2);
        trie.insert("こんにちは", 3);
        trie.insert("世界", 4);

        let mut iter = trie.keys();
        assert_eq!(iter.next(), Some("hello".to_string()));
        assert_eq!(iter.next(), Some("world".to_string()));
        assert_eq!(iter.next(), Some("こんにちは".to_string()));
        assert_eq!(iter.next(), Some("世界".to_string()));
        assert_eq!(iter.next(), None);

        let mut iter = trie.keys().rev();
        assert_eq!(iter.next(), Some("世界".to_string()));
        assert_eq!(iter.next(), Some("こんにちは".to_string()));
        assert_eq!(iter.next(), Some("world".to_string()));
        assert_eq!(iter.next(), Some("hello".to_string()));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn values() {
        let mut trie = TrieMapBase16::new();
        trie.insert("hello", 1);
        trie.insert("world", 2);
        trie.insert("こんにちは", 3);
        trie.insert("世界", 4);

        let mut iter = trie.values();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), None);

        let mut iter = trie.values().rev();
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
    }
}