

use crate::TrieMap;

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