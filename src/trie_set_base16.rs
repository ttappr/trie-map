//! A set implemented as a trie. The keys are strings, which are base 16
//! encoded when stored in the trie. Thus there are no strictions on the
//! range of characters the keys can contain. Each node of the tree has a
//! fixed-size array to its successors (order/branching-factor of 16).
//!

use std::borrow::Borrow;
use std::fmt;

use crate::TrieMap;
use crate::trie_map_base16::{Encoder, decode};

/// A set implemented as a trie that encodes its keys as base 16 bytes.
///
pub struct TrieSetBase16 {
    trie: TrieMap<(), 16, b'a'>,
}

impl TrieSetBase16 {
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
    /// use trie_map::base16::TrieSetBase16;
    ///
    /// let mut set = TrieSetBase16::new();
    ///
    /// assert!(set.insert("hello"));
    ///
    /// assert!(!set.contains("world"));
    /// assert!(set.contains("hello"));
    /// ```
    ///
    pub fn contains(&self, key: &str) -> bool {
        self.trie.contains_by_iter(Encoder::new(key.bytes()))
    }

    /// Reports whether the set contains the given key. The key is given as an
    /// iterator.
    ///
    pub fn contains_by_iter<K>(&self, iter: K) -> bool
    where
        K: Iterator<Item = u8>,
    {
        self.trie.contains_by_iter(iter)
    }

    /// Inserts the given key into the set. Returns true if the key was not
    /// already present.
    ///
    pub fn insert<K>(&mut self, key: K) -> bool
    where
        K: Borrow<str>,
    {
        let iter = Encoder::new(key.borrow().bytes());
        self.trie.insert_by_iter(iter, ()).is_none()
    }

    /// Inserts the given key into the set. Returns true if the key was not
    /// already present.
    ///
    pub fn insert_by_iter<K>(&mut self, iter: K) -> bool
    where
        K: Iterator<Item = u8>,
    {
        self.trie.insert_by_iter(iter, ()).is_none()
    }

    /// Reports whether the set is empty.
    ///
    pub fn is_empty(&self) -> bool {
        self.trie.is_empty()
    }

    /// Returns an iterator over the set.
    ///
    pub fn iter(&self) -> Iter {
        Iter { iter: self.trie.iter() }
    }

    /// Returns an iterator over the set.
    ///
    pub fn len(&self) -> usize {
        self.trie.len()
    }

    /// Removes the given key from the set. Returns true if the key was present.
    ///
    pub fn remove(&mut self, key: &str) -> bool {
        self.trie.remove_by_iter(Encoder::new(key.bytes())).is_some()
    }

    /// Removes the given key from the set. Returns true if the key was present.
    /// The key is given as an iterator.
    ///
    pub fn remove_by_iter<K>(&mut self, iter: K) -> bool
    where
        K: Iterator<Item = u8>,
    {
        self.trie.remove_by_iter(iter).is_some()
    }
}

impl Default for TrieSetBase16 {
    fn default() -> Self {
        Self::new()
    }
}

/// An iterator over the elements of a TrieSet.
///
pub struct Iter<'a> {
    iter: crate::iterators::Iter<'a, (), 16, b'a'>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(key, _)| decode(key))
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(key, _)| decode(key))
    }
}

impl<'a> IntoIterator for &'a TrieSetBase16 {
    type Item = String;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An owning iterator over the elements of a TrieSet.
///
pub struct IntoIter {
    iter: crate::iterators::IntoIter<(), 16, b'a'>,
}

impl DoubleEndedIterator for IntoIter {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(key, _)| decode(key))
    }
}

impl Iterator for IntoIter {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(key, _)| decode(key))
    }
}

impl IntoIterator for TrieSetBase16 {
    type Item = String;
    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { iter: self.trie.into_iter() }
    }
}

impl fmt::Debug for TrieSetBase16 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! s { ($s:expr) => { $s.to_string() } }

    #[test]
    fn clear() {
        let mut set = TrieSetBase16::new();
        set.insert("foo");
        set.insert("bar");
        set.insert("τροφή");
        set.insert("μπαρ");
        assert!(!set.is_empty());
        assert_eq!(set.len(), 4);
        set.clear();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn contains() {
        let mut set = TrieSetBase16::new();
        assert!(!set.contains("foo"));
        set.insert("foo");
        assert!(set.contains("foo"));
        assert!(!set.contains("bar"));
        set.insert("bar");
        assert!(set.contains("foo"));
        assert!(set.contains("bar"));
        assert!(!set.contains("τροφή"));
        assert!(!set.contains("μπαρ"));
    }

    #[test]
    fn fmt_debug() {
        let mut set = TrieSetBase16::new();
        set.insert("foo");
        set.insert("bar");
        set.insert("τροφή");
        set.insert("μπαρ");
        assert_eq!(
            format!("{:?}", set),
            r#"{"bar", "foo", "μπαρ", "τροφή"}"#
        );
    }

    #[test]
    fn insert() {
        let mut set = TrieSetBase16::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        assert!(set.insert("foo"));
        assert!(!set.is_empty());
        assert_eq!(set.len(), 1);
        assert!(set.contains("foo"));
        assert!(!set.contains("bar"));
        assert!(set.insert("bar"));
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn is_empty() {
        let mut set = TrieSetBase16::new();
        assert!(set.is_empty());
        set.insert("foo");
        assert!(!set.is_empty());
        set.remove("bar");
        assert!(!set.is_empty());
        set.remove("foo");
        assert!(set.is_empty());
    }

    #[test]
    fn iter() {
        let mut set = TrieSetBase16::new();
        set.insert("foo");
        set.insert("bar");
        set.insert("τροφή");
        set.insert("μπαρ");
        assert_eq!(
            set.iter().collect::<Vec<_>>(),
            vec![s!("bar"), s!("foo"),
                 s!("μπαρ"), s!("τροφή")]
        );
        assert_eq!(
            set.iter().rev().collect::<Vec<_>>(),
            vec![s!("τροφή"), s!("μπαρ"),
                 s!("foo"), s!("bar")]
        );
        assert_eq!(
            set.into_iter().collect::<Vec<_>>(),
            vec![s!("bar"), s!("foo"),
                 s!("μπαρ"), s!("τροφή")]
        );
    }

    #[test]
    fn len() {
        let mut set = TrieSetBase16::new();
        assert_eq!(set.len(), 0);
        set.insert("foo");
        assert_eq!(set.len(), 1);
        set.insert("bar");
        assert_eq!(set.len(), 2);
        set.remove("bar");
        assert_eq!(set.len(), 1);
        set.remove("foo");
        assert_eq!(set.len(), 0);
    }
}