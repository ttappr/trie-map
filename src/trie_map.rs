//! # TrieMap, A Trie-based Map for Rust
//!
//! This implementation is designed for speed of lookups and insertions. This
//! is achieved by minimizing the number of operations required to access
//! values and leveraging data locality by holding nodes in contiguous memory.
//!
//! Also nodes have fixed size arrays of their descendants, so accessing them
//! isn't likely to result in a cache miss, as could happen if they were stored
//! in a vector or otherwise.
//!
//! The size of the descendant arrays are controlled by the `RANGE` generic
//! parameter. The larger the `RANGE`, the larger the array, the more characters
//! that can be used in keys.
//!
//! The key parameters passed in to the methods of the TrieMap can be
//! `&str`, `String`, `&[u8]`, `Vec<u8>`, or any other type that can be
//! either converted to an iterator over bytes or as a reference to an array of
//! bytes.
//!

use crate::iterators::{Iter, IterMut, Keys, Values};

pub(crate) const ROOT_HANDLE: NodeHandle = NodeHandle(0);

/// A handle used interally to reference values stored in the trie.
///
#[repr(transparent)]
#[derive(Copy, Clone)]
pub(crate) struct ValueHandle(pub(crate) usize);

/// A handle used interally to reference nodes stored in the trie.
///
#[repr(transparent)]
#[derive(Copy, Clone)]
pub(crate) struct NodeHandle(pub(crate) usize);

/// This is a struct used internally by the TrieMap to represent a node in the
/// trie. If it's a leaf node, it will have a value. If it's an internal node,
/// it will have a value of None. The `child` array is used to reference the
/// next descendant nodes indexed by the byte value of the next character in
/// the key.
///
/// `RANGE` controls the size of the `child` array. The larger the `RANGE`, the
/// larger the array, the more characters that can be used in keys, however at
/// the cost of some more memory usage.
///
pub(crate) struct Node<const RANGE: usize> {
    pub(crate) child : [Option<NodeHandle>; RANGE],
    pub(crate) value : Option<ValueHandle>,
    pub(crate) len   : usize,
}
impl<const RANGE: usize> Node<RANGE> {
    fn new() -> Self {
        Self { child: [None; RANGE], value: None, len: 0 }
    }
}

/// A trie-based Map keyed on sequences of bytes with values stored at the
/// leaves of the trie. `RANGE` controls the size of the `child` array in each
/// node. And `BASE_CHAR` is the byte value of the first character in the range
/// of characters that can be used in keys. It is used to adjust each character
/// in a key to serve as indices into the their descendant arrays.
///
pub struct TrieMap<V, const RANGE: usize, const BASE_CHAR: u8> {
    pub(crate) root      : NodeHandle,
    pub(crate) nodes     : Vec<Node<RANGE>>,
    pub(crate) values    : Vec<Option<V>>,
    pub(crate) node_bin  : Vec<NodeHandle>,
    pub(crate) value_bin : Vec<ValueHandle>,
    pub(crate) len       : usize,
}
impl<V, const RANGE: usize, const BASE_CHAR: u8> TrieMap<V, RANGE, BASE_CHAR> {
    /// Creates a new empty trie.
    ///
    pub fn new() -> Self {
        Self {
            root      : ROOT_HANDLE,
            nodes     : vec![Node::new()],
            values    : vec![],
            node_bin  : vec![],
            value_bin : vec![],
            len       : 0,
        }
    }

    /// Creates a new empty trie with the given capacity. Only the internal
    /// vector that holds the values is affected by this method.
    ///
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            root      : ROOT_HANDLE,
            nodes     : vec![Node::new()],
            values    : Vec::with_capacity(capacity),
            node_bin  : vec![],
            value_bin : vec![],
            len       : 0,
        }
    }

    /// Clears the trie, removing all values.
    /// 
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.values.clear();
        self.node_bin.clear();
        self.value_bin.clear();
        self.len = 0;
    }

    /// Returns `true` if the trie contains a value at the given key, otherwise
    /// `false` is returned.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert("hello", 1);
    ///
    /// assert_eq!(trie.contains("hello"), true);
    /// ```
    ///
    pub fn contains<K>(&self, key: K) -> bool
    where
        K: AsRef<[u8]>,
    {
        self.contains_by_iter(key.as_ref().into_iter().copied())
    }

    /// Returns `true` if the trie contains a value at the given key, otherwise
    /// `false` is returned. The trait bound on `K` is makes it easy to pass an
    /// iterator or other type that can be converted into an iterator as a
    /// paramter.
    /// ```
    /// use trie_map::TrieMap;
    /// use std::collections::VecDeque;
    /// 
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    /// 
    /// trie.insert(b"hello", 1);
    /// 
    /// let mut window = b"hhell".iter().copied().collect::<VecDeque<_>>();
    /// 
    /// window.pop_front();
    /// window.push_back(b'o');
    /// 
    /// assert_eq!(trie.contains_by_iter(window.range(0..5).copied()), true);
    /// ```
    pub fn contains_by_iter<K>(&self, key: K) -> bool
    where
        K: Iterator<Item=u8>,
    {
        let mut key   = key;
        let mut hcurr = self.root;
        while let Some(b) = key.next() {
            let ichild = (b - BASE_CHAR) as usize;
            if let Some(hnext) = self.hderef(hcurr).child[ichild] {
                hcurr = hnext;
            } else {
                return false;
            }
        }
        self.hderef(hcurr).value.is_some()
    }

    /// Accesses a value in the trie at the given key, if it exists, a reference
    /// is returned, otherwise `None` is returned.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert("hello", 1);
    ///
    /// assert_eq!(trie.get("hello"), Some(&1));
    /// assert_eq!(trie.get("world"), None);
    /// ```
    pub fn get<K>(&self, key: K) -> Option<&V>
    where
        K: AsRef<[u8]>,
    {
        self.get_by_iter(key.as_ref().into_iter().copied())
    }

    /// Accesses a value in the trie at the given key, if it exists, a reference
    /// is returned, otherwise `None` is returned. The trait bound on `K` is
    /// makes it easy to pass an iterator or other type that can be converted
    /// into an iterator as a paramter.
    /// ```
    /// use trie_map::TrieMap;
    /// use std::collections::VecDeque;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert("hello", 1);
    ///
    /// let mut window = b"hhell".iter().copied().collect::<VecDeque<_>>();
    ///
    /// window.pop_front();
    /// window.push_back(b'o');
    ///
    /// assert_eq!(trie.get_by_iter(window.range(0..5).copied()), Some(&1));
    /// ````
    pub fn get_by_iter<K>(&self, key: K) -> Option<&V>
    where
        K: Iterator<Item=u8>,
    {
        let mut key   = key;
        let mut hcurr = self.root;
        while let Some(b) = key.next() {
            debug_assert!(b >= BASE_CHAR && b < BASE_CHAR + RANGE as u8);
            let ichild = (b - BASE_CHAR) as usize;
            if let Some(hnext) = self.hderef(hcurr).child[ichild] {
                hcurr = hnext;
            } else {
                return None;
            }
        }
        if let Some(hvalue) = self.hderef(hcurr).value {
            self.values[hvalue.0].as_ref()
        } else {
            None
        }
    }

    /// Returns a mutable reference to a value in the trie at the given key, if
    /// it exists, otherwise `None` is returned.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert("hello", 1);
    ///
    /// *trie.get_mut("hello").unwrap() = 17;
    ///
    /// assert_eq!(trie.get("hello"), Some(&17));
    /// ```
    pub fn get_mut<K>(&mut self, key: K) -> Option<&mut V>
    where
        K: AsRef<[u8]>,
    {
        self.get_mut_by_iter(key.as_ref().into_iter().copied())
    }

    /// Returns a mutable reference to a value in the trie at the given key, if
    /// it exists, otherwise `None` is returned. The trait bound on `K` is
    /// makes it easy to pass an iterator or other type that can be converted
    /// into an iterator as a paramter.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert(b"hello", 1);
    /// 
    /// let iter = b"hel".iter().chain(b"lo").copied();
    /// 
    /// *trie.get_mut_by_iter(iter).unwrap() = 17;
    /// 
    /// assert_eq!(trie.get(b"hello"), Some(&17));
    /// ```
    pub fn get_mut_by_iter<'a, K>(&mut self, key: K) -> Option<&mut V>
    where
        K: Iterator<Item=u8>,
    {
        let mut key   = key;
        let mut hcurr = self.root;
        while let Some(b) = key.next() {
            debug_assert!(b >= BASE_CHAR && b < BASE_CHAR + RANGE as u8);
            let ichild = (b - BASE_CHAR) as usize;
            if let Some(hnext) = self.hderef(hcurr).child[ichild] {
                hcurr = hnext;
            } else {
                return None;
            }
        }
        if let Some(hvalue) = self.hderef(hcurr).value {
            self.values[hvalue.0].as_mut()
        } else {
            None
        }
    }

    /// Returns a mutable reference to a value in the trie at the given key, if
    /// it exists, otherwise the given value is inserted and a reference to it
    /// is returned.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// assert_eq!(trie.get_or_insert("hello", 1), &1);
    /// ```
    pub fn get_or_insert<K>(&mut self, key: K, value: V) -> &mut V
    where
        K: AsRef<[u8]>,
    {
        let iter = key.as_ref().into_iter().copied();
        self.get_or_insert_by_iter_with(iter, ||value)
    }

    /// Returns a mutable reference to a value in the trie at the given key, if
    /// it exists, otherwise the given value is inserted and a reference to it
    /// is returned. The trait bound on `K` is makes it easy to pass an iterator
    /// or other type that can be converted into an iterator as a paramter.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// let iter = b"hello".iter().chain(b"world").copied();
    ///
    /// *trie.get_or_insert_by_iter(iter, 1) = 17;
    ///
    /// assert_eq!(trie.get(b"helloworld"), Some(&17));
    /// ```
    pub fn get_or_insert_by_iter<'a, K>(&mut self, key: K, value: V) -> &mut V
    where
        K: Iterator<Item=u8>,
    {
        self.get_or_insert_by_iter_with(key, ||value)
    }

    /// Returns a mutable reference to a value in the trie at the given key, if
    /// it exists, otherwise the given function is called to produce a value
    /// which is inserted and a reference to it is returned.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// assert_eq!(trie.get_or_insert_with("hello", ||1), &1);
    /// ```
    ///
    pub fn get_or_insert_with<K, F>(&mut self, key: K, f: F) -> &mut V
    where
        K: AsRef<[u8]>,
        F: FnOnce() -> V,
    {
        let iter = key.as_ref().into_iter().copied();
        self.get_or_insert_by_iter_with(iter, f)
    }

    /// Returns a mutable reference to a value in the trie at the given key, if
    /// it exists, otherwise the given function is called to produce a value
    /// which is inserted and a reference to it is returned. The trait bound on
    /// `K` enables passing an iterator or other type that can be converted into
    /// an iterator as a paramter.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// let iter = b"hello".iter().chain(b"world").copied();
    ///
    /// *trie.get_or_insert_by_iter_with(iter, ||1) = 17;
    ///
    /// assert_eq!(trie.get(b"helloworld"), Some(&17));
    /// ```
    pub fn get_or_insert_by_iter_with<'a, K, F>(&mut self, key: K, f: F)
        -> &mut V
    where
        K: Iterator<Item=u8>,
        F: FnOnce() -> V,
    {
        let mut key   = key;
        let mut hcurr = self.root;
        while let Some(b) = key.next() {
            debug_assert!(b >= BASE_CHAR && b < BASE_CHAR + RANGE as u8);
            let ichild = (b - BASE_CHAR) as usize;
            if let Some(hnext) = self.hderef(hcurr).child[ichild] {
                hcurr = hnext;
            } else {
                let hnew = self.new_node();
                let curr = self.hderef_mut(hcurr);
                curr.child[ichild] = Some(hnew);
                curr.len += 1;
                hcurr = hnew;
            }
        }
        let hvalue = {
            if let Some(hvalue) = self.hderef(hcurr).value {
                hvalue
            } else {
                let hvalue = self.new_value(f());
                self.hderef_mut(hcurr).value = Some(hvalue);
                hvalue
            }
        };
        self.values[hvalue.0].as_mut().unwrap()
    }

    /// Inserts a value into the trie at the given key. If the key already
    /// exists in the trie, the value is replaced and the old value is returned,
    /// otherwise `None` is returned.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert("hello", 1);
    ///
    /// assert_eq!(trie.get("hello"), Some(&1));
    /// ```
    pub fn insert<K>(&mut self, key: K, value: V) -> Option<V>
    where
        K: AsRef<[u8]>,
    {
        self.insert_by_iter(key.as_ref().into_iter().copied(), value)
    }

    /// Inserts a value into the trie at the given key. The trait bound on `K`
    /// makes it easy to pass an iterator or other type that can be converted
    /// into an iterator as a paramter. If the key already exists in the trie,
    /// the value is replaced and the old value is returned, otherwise `None` is
    /// returned.
    ///
    pub fn insert_by_iter<'a, K>(&mut self, key: K, value: V) -> Option<V>
    where
        K: Iterator<Item=u8>,
    {
        let mut key    = key;
        let mut hcurr  = self.root;
        let mut retval = None;
        while let Some(b) = key.next() {
            debug_assert!(b >= BASE_CHAR && b < BASE_CHAR + RANGE as u8);
            let ichild = (b - BASE_CHAR) as usize;
            if let Some(hnext) = self.hderef(hcurr).child[ichild] {
                hcurr = hnext;
            } else {
                let hnew = self.new_node();
                let curr = self.hderef_mut(hcurr);
                curr.child[ichild] = Some(hnew);
                curr.len += 1;
                hcurr = hnew;
            }
        }
        if let Some(hvalue) = self.hderef_mut(hcurr).value {
            retval = self.values[hvalue.0].take();
        }
        let hvalue = self.new_value(value);
        self.hderef_mut(hcurr).value = Some(hvalue);
        retval
    }

    /// Returns an iterator over the key-value pairs in the trie.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert("hello", 1);
    /// trie.insert("world", 2);
    ///
    /// let mut iter  = trie.iter();
    /// let     first = iter.next().unwrap();
    ///
    /// assert_eq!(first.0.as_ref(), b"hello");
    /// assert_eq!(first.1, &1);
    ///
    /// ```
    pub fn iter(&self) -> Iter<V, RANGE, BASE_CHAR> {
        Iter::new(self)
    }

    /// Returns an iterator over the mutable key-value pairs in the trie. Only
    /// the values are mutable, not the keys.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert("hello", 1);
    /// trie.insert("world", 2);
    ///
    /// let mut iter  = trie.iter_mut();
    /// let     first = iter.next().unwrap();
    /// *first.1 = 17;
    ///
    /// assert_eq!(trie.get("hello"), Some(&17));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<V, RANGE, BASE_CHAR> {
        IterMut::new(self)
    }

    /// Returns an iterator over the keys in the trie.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert("hello", 1);
    ///
    /// assert_eq!(trie.keys().next().unwrap().as_ref(), b"hello");
    /// ```
    pub fn keys(&self) -> Keys<V, RANGE, BASE_CHAR> {
        Keys::new(self)
    }

    /// Returns the number of values in the trie.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::with_capacity(10);
    ///
    /// trie.insert("hello", 1);
    ///
    /// assert_eq!(trie.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the trie contains no values, otherwise `false` is
    /// returned.
    /// ```
    /// use trie_map::TrieMap;
    /// 
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::with_capacity(10);
    /// 
    /// assert_eq!(trie.is_empty(), true);
    /// 
    /// trie.insert("hello", 1);
    /// 
    /// assert_eq!(trie.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Removes a value from the trie at the given key, if it exists, and
    /// returns it, otherwise `None` is returned.
    ///
    pub fn remove<K>(&mut self, key: K) -> Option<V>
    where
        K: AsRef<[u8]>,
    {
        self.remove_by_iter(key.as_ref().into_iter().copied())
    }

    /// Removes a value from the trie at the given key, if it exists, and
    /// returns it, otherwise `None` is returned. The trait bound on `K` makes
    /// it easy to pass an iterator or other type that can be converted into an
    /// iterator as a paramter as the key.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::with_capacity(10);
    ///
    /// trie.insert("hello", 1);
    ///
    /// assert_eq!(trie.remove_by_iter("hello".bytes()), Some(1));
    /// ```
    pub fn remove_by_iter<'a, K>(&mut self, key: K) -> Option<V>
    where
        K: Iterator<Item=u8>,
    {
        let mut key   = key;
        let mut hcurr = self.root;
        let mut stack = Vec::new();
        while let Some(b) = key.next() {
            debug_assert!(b >= BASE_CHAR && b < BASE_CHAR + RANGE as u8);
            let ichild = (b - BASE_CHAR) as usize;
            if let Some(hnext) = self.hderef(hcurr).child[ichild] {
                stack.push((hcurr, ichild));
                hcurr = hnext;
            } else {
                return None;
            }
        }
        // Clean up the nodes that are no longer needed.
        if let Some(hvalue) = self.hderef(hcurr).value {
            self.hderef_mut(hcurr).value = None;
            self.del_value(hvalue);
            let value = self.values[hvalue.0].take().unwrap();
            if self.hderef(hcurr).len == 0 {
                self.del_node(hcurr);
                while let Some((hnode, ichild)) = stack.pop() {
                    let node = self.hderef_mut(hnode);
                    node.child[ichild] = None;
                    node.len -= 1;
                    if node.len == 0 && node.value.is_none() {
                        self.del_node(hnode);
                    } else {
                        break;
                    }
                }
            }
            Some(value)
        } else {
            None
        }
    }

    /// Returns an iterator over the values in the trie.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert(b"hello", 1);
    ///
    /// assert_eq!(trie.values().next(), Some(&1));
    /// ```
    pub fn values(&self) -> Values<V, RANGE, BASE_CHAR> {
        Values::new(self)
    }

    /// Used internally to create a new node and return a handle to it.
    ///
    #[inline]
    fn new_node(&mut self) -> NodeHandle {
        if let Some(handle) = self.node_bin.pop() {
            handle
        } else {
            self.nodes.push(Node::new());
            NodeHandle(self.nodes.len() - 1)
        }
    }

    /// Used internally to add a new value to the internal values vector and
    /// return a handle to it.
    ///
    #[inline]
    fn new_value(&mut self, value: V) -> ValueHandle {
        if let Some(hvalue) = self.value_bin.pop() {
            self.values[hvalue.0] = Some(value);
            hvalue
        } else {
            self.values.push(Some(value));
            self.len += 1;
            ValueHandle(self.values.len() - 1)
        }
    }

    /// Used internally to delete a node handle. The handle is actually added
    /// to a bin for reuse.
    ///
    #[inline]
    fn del_node(&mut self, handle: NodeHandle) {
        self.node_bin.push(handle);
    }

    /// Used internally to delete a value handle. The handle is actually added
    /// to a bin for reuse.
    ///
    #[inline]
    fn del_value(&mut self, handle: ValueHandle) {
        self.len -= 1;
        self.value_bin.push(handle);
    }

    /// Used internally to dereference a node handle.
    ///
    #[inline(always)]
    pub(crate) fn hderef(&self, handle: NodeHandle) -> &Node<RANGE> {
        &self.nodes[handle.0]
    }

    /// Used internally to dereference a node handle mutably.
    ///
    #[inline(always)]
    pub(crate) fn hderef_mut(&mut self, handle: NodeHandle) 
        -> &mut Node<RANGE> 
    {
        &mut self.nodes[handle.0]
    }
}

impl<V, const R: usize, const B: u8> Default for TrieMap<V, R, B> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contains() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);

        assert_eq!(trie.contains(b"hello"), true);
        assert_eq!(trie.contains(b"world"), false);

        trie.insert(b"world", 2);

        assert_eq!(trie.contains(b"hello"), true);
        assert_eq!(trie.contains(b"world"), true);
    }

    #[test]
    fn get() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        assert_eq!(trie.get(b"hello"), Some(&1));
        assert_eq!(trie.get(b"world"), Some(&2));
        assert_eq!(trie.get(b"walter"), None);

        trie.insert(&[b'w', b'a', b'l', b't', b'e', b'r'], 3);

        assert_eq!(trie.get(b"walter"), Some(&3));
    }

    #[test]
    fn get_mut() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        assert_eq!(trie.get_mut(b"hello"), Some(&mut 1));
        assert_eq!(trie.get_mut(b"world"), Some(&mut 2));
        assert_eq!(trie.get_mut(b"walter"), None);

        *trie.get_mut(b"world").unwrap() = 17;

        assert_eq!(trie.get_mut(b"world"), Some(&mut 17));
    }

    #[test]
    fn get_or_insert() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        assert_eq!(trie.get_or_insert(b"hello", 3), &1);
        assert_eq!(trie.get_or_insert(b"world", 3), &2);
        assert_eq!(trie.get_or_insert(b"walter", 3), &3);

        assert_eq!(trie.get(b"hello"), Some(&1));
        assert_eq!(trie.get(b"world"), Some(&2));
        assert_eq!(trie.get(b"walter"), Some(&3));
    }

    #[test]
    fn get_or_insert_with() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        assert_eq!(trie.get_or_insert_with(b"hello", ||3), &1);
        assert_eq!(trie.get_or_insert_with(b"world", ||3), &2);
        assert_eq!(trie.get_or_insert_with(b"walter", ||3), &3);

        assert_eq!(trie.get(b"hello"), Some(&1));
        assert_eq!(trie.get(b"world"), Some(&2));
        assert_eq!(trie.get(b"walter"), Some(&3));
    }

    #[test]
    fn insert() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        assert_eq!(trie.get(b"hello"), Some(&1));
        assert_eq!(trie.get(b"world"), Some(&2));
        assert_eq!(trie.get(b"walter"), None);

        trie.insert(&[b'w', b'a', b'l', b't', b'e', b'r'], 3);
    }

    #[test]
    fn len() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        assert_eq!(trie.len(), 0);

        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);
        assert_eq!(trie.len(), 2);
        trie.insert(b"walter", 3);
        assert_eq!(trie.len(), 3);
        trie.remove(b"hello");
        assert_eq!(trie.len(), 2);
        trie.remove(b"world");
        assert_eq!(trie.len(), 1);
        trie.remove(b"walter");
        assert_eq!(trie.len(), 0);
    }

    #[test]
    fn remove() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        assert_eq!(trie.remove(b"walter"), None);
        assert_eq!(trie.remove(b"world"), Some(2));
        assert_eq!(trie.remove(b"hello"), Some(1));

        assert_eq!(trie.remove(b"walter"), None);
        assert_eq!(trie.remove(b"world"), None);
        assert_eq!(trie.remove(b"hello"), None);
    }

    #[test]
    fn values() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [(b"hello", 1), (b"world", 2)];

        for (key, val) in &data {
            trie.insert(key, *val);
        }
        for (&val1, &val2) in trie.values().zip(data.iter().map(|(_, v)| v)) {
            assert_eq!(val1, val2);
        }
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [("hello", 1), ("hellowalterjack", 2), ("world", 3)];

        for &(key, val) in &data {
            trie.insert(key, val);
        }
        let iter = trie.values().zip(data.iter().map(|(_, v)| v));

        for (&val1, &val2) in iter {
            assert_eq!(val1, val2);
        }
    }
}
