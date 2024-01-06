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
/// 
pub struct TrieMapBase26<V> {
    trie: TrieMap<V, 16, b'a'>,
}

impl<V> TrieMapBase26<V> { 
    pub fn new() -> Self {
        Self { trie: TrieMap::new() }
    }

    pub fn contains(&self, key: &str) -> bool {
        self.trie.get_by_iter(Encoder::new(key.bytes())).is_some()
    }

    pub fn get(&self, key: &str) -> Option<&V> {
        self.trie.get_by_iter(Encoder::new(key.bytes()))
    }

    pub fn get_mut(&mut self, key: &str) -> Option<&mut V> {
        self.trie.get_mut_by_iter(Encoder::new(key.bytes()))
    }

    pub fn insert<K: Borrow<str>>(&mut self, key: K, value: V) -> Option<V> {
        self.trie.insert_by_iter(Encoder::new(key.borrow().bytes()), value)
    }

    pub fn len(&self) -> usize {
        self.trie.len()
    }

    pub fn is_empty(&self) -> bool {
        self.trie.is_empty()
    }

    pub fn remove(&mut self, key: &str) -> Option<V> {
        self.trie.remove_by_iter(Encoder::new(key.bytes()))
    }

    pub fn clear(&mut self) {
        self.trie.clear();
    }
}

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

    fn next(&mut self) -> Option<Self::Item> {
        if self.buf > 0 {
            let b = self.buf;
            self.buf = 0;
            Some(b)
        } else if let Some(b) = self.key.next() {
            self.buf = b & 0x0f;
            let b = b >> 4;
            Some(b)
        } else {
            None
        }
    }
}
