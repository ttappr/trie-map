//! A set implemented using TrieMap.
//! 

use crate::TrieMap;

/// A set implemented using TrieMap. Internally this is a TrieMap with a unit
/// type as the value. This is a convenience type for when you want to use a
/// TrieMap as a set.
/// 
pub struct TrieSet<const R: usize, const B: u8> {
    trie: TrieMap<(), R, B>
}

impl<const R: usize, const B: u8> TrieSet<R, B> {
    pub fn new() -> Self {
        Self { trie: TrieMap::new() }
    }

    pub fn contains<K: AsRef<[u8]>>(&self, key: K) -> bool {
        self.trie.get(key).is_some()
    }

    pub fn get<K: AsRef<[u8]>>(&self, key: K) -> Option<&()> {
        self.trie.get(key)
    }

    pub fn insert<K: AsRef<[u8]>>(&mut self, key: K) -> bool {
        self.trie.insert(key, ()).is_none()
    }

    pub fn len(&self) -> usize {
        self.trie.len()
    }

    pub fn is_empty(&self) -> bool {
        self.trie.is_empty()
    }

    pub fn remove<K: AsRef<[u8]>>(&mut self, key: K) -> bool {
        self.trie.remove(key).is_some()
    }

    pub fn clear(&mut self) {
        self.trie.clear();
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trie_set() {
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
        assert!(!set.contains("hello"));
        assert!(set.contains("world"));
        assert!(!set.contains("hell"));
        assert!(!set.contains("worl"));
        assert!(!set.contains("helloworld"));
        assert!(!set.contains("worldhello"));
        assert!(!set.contains("helloworld!"));
        assert!(!set.contains("worldhello!"));
        assert!(set.remove("world"));
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        assert!(!set.contains("hello"));
        assert!(!set.contains("world"));
        assert!(!set.contains("hell"));
        assert!(!set.contains("worl"));
        assert!(!set.contains("helloworld"));
        assert!(!set.contains("worldhello"));
        assert!(!set.contains("helloworld!"));
        assert!(!set.contains("worldhello!"));
    }
}