//! A set implemented using TrieMap.
//!

use std::fmt;

use crate::TrieMap;
use crate::trie_map_iterators;

/// A set implemented using TrieMap. Internally this is a TrieMap with a unit
/// type as the value. This is a convenience type for when you want to use a
/// TrieMap as a set.
///
pub struct TrieSet<const R: usize, const B: u8> {
    trie: TrieMap<(), R, B>
}

impl<const R: usize, const B: u8> TrieSet<R, B> {
    /// Creates a new empty TrieSet.
    ///
    pub fn new() -> Self {
        Self { trie: TrieMap::new() }
    }

    /// Removes all elements from the set.
    ///
    pub fn clear(&mut self) {
        self.trie.clear();
    }

    /// Reports whether the set contains the given key.
    /// ```
    /// use trie_map::TrieSet;
    ///
    /// let mut set = TrieSet::<26, b'a'>::new();
    ///
    /// assert!(set.insert("hello"));
    /// assert!(set.contains("hello"));
    /// assert!(!set.contains("world"));
    /// ````
    pub fn contains<K>(&self, key: K) -> bool 
    where
        K: AsRef<[u8]>
    {
        self.trie.get(key).is_some()
    }

    /// Reports whether the set contains the given key. The key is given as an
    /// iterator.
    /// ```
    /// use trie_map::TrieSet;
    ///
    /// let mut set = TrieSet::<26, b'a'>::new();
    ///
    /// assert!(set.insert("hello"));
    /// assert!(set.contains_by_iter("hello".bytes()));
    /// assert!(!set.contains_by_iter("world".bytes()));
    /// ```
    pub fn contains_by_iter<K>(&self, key: K) -> bool
    where
        K: Iterator<Item = u8>
    {
        self.trie.contains_by_iter(key)
    }

    /// Inserts the given key into the set. Returns true if the key was not
    /// already present.
    /// ```
    /// use trie_map::TrieSet;
    ///
    /// let mut set = TrieSet::<26, b'a'>::new();
    ///
    /// assert!(set.insert("hello"));
    /// assert!(!set.insert("hello"));
    /// assert!(set.insert("world"));
    /// ````
    pub fn insert<K>(&mut self, key: K) -> bool 
    where
        K: AsRef<[u8]>
    {
        self.trie.insert(key, ()).is_none()
    }

    /// Inserts the given key into the set. Returns true if the key was not
    /// already present. The key is given as an iterator.
    ///
    pub fn insert_by_iter<K>(&mut self, key: K) -> bool
    where
        K: Iterator<Item = u8>
    {
        self.trie.insert_by_iter(key, ()).is_none()
    }

    /// Returns true if the set contains no elements.
    ///
    pub fn is_empty(&self) -> bool {
        self.trie.is_empty()
    }

    /// Returns an iterator over the keys of the set.
    ///
    pub fn iter(&self) -> Iter<R, B> {
        self.into_iter()
    }

    /// Returns the number of elements in the set.
    ///
    pub fn len(&self) -> usize {
        self.trie.len()
    }

    /// Removes the given key from the set. Returns true if the key was present.
    ///
    pub fn remove<K>(&mut self, key: K) -> bool 
    where
        K: AsRef<[u8]>
    {
        self.trie.remove(key).is_some()
    }

    /// Removes the given key from the set. Returns true if the key was present.
    /// The key is given as an iterator.
    /// ```
    /// use trie_map::TrieSet;
    ///
    /// let mut set = TrieSet::<26, b'a'>::new();
    ///
    /// assert!(set.insert("hello"));
    /// assert!(set.remove_by_iter("hello".bytes()));
    /// assert!(!set.remove_by_iter("hello".bytes()));
    /// ```
    pub fn remove_by_iter<K>(&mut self, key: K) -> bool
    where
        K: Iterator<Item = u8>
    {
        self.trie.remove_by_iter(key).is_some()
    }
}

impl<const R: usize, const B: u8> Default for TrieSet<R, B> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct IntoIter<const R: usize, const B: u8> {
    iter: trie_map_iterators::IntoIter<(), R, B>,
}

impl<const R: usize, const B: u8> Iterator for IntoIter<R, B> {
    type Item = Box<[u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, _)| k)
    }
}

impl<const R: usize, const B: u8> DoubleEndedIterator for IntoIter<R, B> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, _)| k)
    }
}

impl<'a, const R: usize, const B: u8> IntoIterator for TrieSet<R, B> {
    type Item = Box<[u8]>;
    type IntoIter = IntoIter<R, B>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { iter: self.trie.into_iter() }
    }
}

pub struct Iter<'a, const R: usize, const B: u8> {
    iter: trie_map_iterators::Iter<'a, (), R, B>,
}

impl<'a, const R: usize, const B: u8> Iterator for Iter<'a, R, B> {
    type Item = Box<[u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, _)| k)
    }
}

impl<'a, const R: usize, const B: u8> DoubleEndedIterator for Iter<'a, R, B> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, _)| k)
    }
}

impl<'a, const R: usize, const B: u8> IntoIterator for &'a TrieSet<R, B> {
    type Item = Box<[u8]>;
    type IntoIter = Iter<'a, R, B>;

    fn into_iter(self) -> Self::IntoIter {
        Iter { iter: self.trie.iter() }
    }
}

impl<const R: usize, const B: u8> fmt::Debug for TrieSet<R, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.trie.keys()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bx(s: &str) -> Box<[u8]> {
        s.as_bytes().to_vec().into_boxed_slice()
    }

    #[test]
    fn contains() {
        let mut set = TrieSet::<26, b'a'>::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        assert!(set.insert("hello"));
        assert!(set.insert("world"));
        assert_eq!(set.len(), 2);
        assert!(!set.is_empty());
        assert!(set.contains("hello"));
        assert!(set.contains("world"));
        assert!(!set.contains("hell"));
        assert!(!set.contains("worl"));
        assert!(!set.contains("helloworld"));
        assert!(!set.contains("worldhello"));
        assert!(!set.contains("helloworld!"));
        assert!(!set.contains("worldhello!"));
        assert!(set.remove("hello"));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn iter() {
        let mut set = TrieSet::<26, b'a'>::new();
        assert!(set.insert("hello"));
        assert!(set.insert("world"));
        assert_eq!(set.iter().collect::<Vec<_>>(),
                   vec![bx("hello"), bx("world")]);
    }

    #[test]
    fn iter_rev() {
        let mut set = TrieSet::<26, b'a'>::new();
        assert!(set.insert("hello"));
        assert!(set.insert("world"));
        assert_eq!(set.iter().rev().collect::<Vec<_>>(),
                   vec![bx("world"), bx("hello")]);
    }

    #[test]
    fn into_iter() {
        let mut set = TrieSet::<26, b'a'>::new();
        assert!(set.insert("hello"));
        assert!(set.insert("world"));
        assert_eq!(set.into_iter().collect::<Vec<_>>(),
                   vec![bx("hello"), bx("world")]);
    }

    #[test]
    fn fmt_debug() {
        let mut set = TrieSet::<26, b'a'>::new();
        assert!(set.insert("hello"));
        assert!(set.insert("world"));
        assert_eq!(format!("{:?}", set),
                   r#"{[104, 101, 108, 108, 111], "#.to_owned()
                   + r#"[119, 111, 114, 108, 100]}"#);
    }
}