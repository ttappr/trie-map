#![allow(dead_code)]

use std::borrow::Borrow;

use crate::TrieMap;

/// A trie whose keys are primarily sequences of lowercase ASCII letters, but
/// can also contain any other character using a special escape sequence.
///
/// This strategy is transparent to the user. The user could pass in strings
/// containing all Greek characters if they wanted, it just takes more syntax
/// nodes to store them. So if keys are primarily lowercase ASCII, this trie
/// should be very efficient while providing some additional key flexibility.
///
/// Any character in a string that isn't lowercase ASCII is escaped with a
/// 'q' followed by the character's encoded value using two lowercase ASCII
/// characters to represent any byte value from 0 to 255. The key encoder will
/// remain in the escaped state until it encounters a lowercase ASCII letter,
/// at which point it will terminate the encoded region of the key with a single
/// 'q'.
/// 
/// The encoder is implemented as an iterator, so only the necessary number of
/// key characters are processed in cases where a `get` operation is being
/// performed and the key isn't in the trie. It will give up early, minimizing
/// the operations performed during a lookup miss.
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
