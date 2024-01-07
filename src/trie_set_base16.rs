
use std::borrow::Borrow;

use crate::TrieMap;
use crate::trie_map_base16::{Encoder, decode};

pub struct TrieSetBase16 {
    trie: TrieMap<(), 16, b'a'>,
}

impl TrieSetBase16 {
    pub fn new() -> Self {
        Self { trie: TrieMap::new() }
    }

    pub fn clear(&mut self) {
        self.trie.clear();
    }

    pub fn contains(&self, key: &str) -> bool {
        self.trie.contains_by_iter(Encoder::new(key.bytes()))
    }

    pub fn insert<K>(&mut self, key: K) -> bool 
    where
        K: Borrow<str>,
    {
        let iter = Encoder::new(key.borrow().bytes());
        self.trie.insert_by_iter(iter, ()).is_none()
    }

    pub fn is_empty(&self) -> bool {
        self.trie.is_empty()
    }

    pub fn iter(&self) -> Iter {
        Iter { iter: self.trie.iter() }
    }

    pub fn len(&self) -> usize {
        self.trie.len()
    }

    pub fn remove(&mut self, key: &str) -> bool {
        self.trie.remove_by_iter(Encoder::new(key.bytes())).is_some()
    }
}

impl Default for TrieSetBase16 {
    fn default() -> Self {
        Self::new()
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trie_set_base16() {
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
        assert!(set.contains("bar"));
        assert!(set.remove("foo"));
        assert_eq!(set.len(), 1);
        assert!(!set.contains("foo"));
        assert!(set.contains("bar"));
        assert!(set.insert("foo"));
        assert_eq!(set.len(), 2);
        assert!(set.contains("foo"));
        assert!(set.contains("bar"));
        assert!(!set.insert("foo"));
        assert_eq!(set.len(), 2);
        assert!(set.contains("foo"));
        assert!(set.contains("bar"));
        assert!(!set.insert("bar"));
        assert_eq!(set.len(), 2);
        assert!(set.contains("foo"));
        assert!(set.contains("bar"));
        assert_eq!(
            set.into_iter().collect::<Vec<_>>(),
            vec!["bar".to_string(), "foo".to_string()]
        );
    }
}