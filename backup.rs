//! # TrieMap, A Trie-based Map for Rust
//!
//! This implementation is designed for speed of lookups, insertions, etc. This
//! is achieved by minimizing the number of operations required to access
//! values and optimizing data locality by holding nodes in contiguous memory.
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

/// A handle used interally to reference values stored in the trie.
///
#[repr(transparent)]
#[derive(Copy, Clone)]
struct ValueHandle(usize);

/// A handle used interally to reference nodes stored in the trie.
///
#[repr(transparent)]
#[derive(Copy, Clone)]
struct NodeHandle(usize);

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
struct Node<const RANGE: usize> {
    child : [Option<NodeHandle>; RANGE],
    value : Option<ValueHandle>,
    len   : usize,
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
    root      : NodeHandle,
    nodes     : Vec<Node<RANGE>>,
    values    : Vec<Option<V>>,
    node_bin  : Vec<NodeHandle>,
    value_bin : Vec<ValueHandle>,
    len       : usize,
}
impl<V, const RANGE: usize, const BASE_CHAR: u8> TrieMap<V, RANGE, BASE_CHAR> {
    /// Creates a new empty trie.
    ///
    pub fn new() -> Self {
        Self {
            root      : NodeHandle(0),
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
            root      : NodeHandle(0),
            nodes     : vec![Node::new()],
            values    : Vec::with_capacity(capacity),
            node_bin  : vec![],
            value_bin : vec![],
            len       : 0,
        }
    }

    /// Returns `true` if the trie contains a value at the given key, otherwise
    /// `false` is returned.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert(b"hello", 1);
    ///
    /// assert_eq!(trie.contains(b"hello"), true);
    /// ```
    ///
    pub fn contains<K>(&self, key: K) -> bool
    where
        K: AsRef<[u8]>,
    {
        let mut curr = self.root;
        for b in key.as_ref() {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(curr).child[idx] {
                curr = next;
            } else {
                return false;
            }
        }
        self.hderef(curr).value.is_some()
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
        self.get_by_iter(key.as_ref())
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
    /// assert_eq!(trie.get_by_iter(window.range(0..5)), Some(&1));
    /// ````
    pub fn get_by_iter<'a, K>(&self, key: K) -> Option<&V>
    where
        K: IntoIterator<Item=&'a u8>,
    {
        let mut curr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(curr).child[idx] {
                curr = next;
            } else {
                return None;
            }
        }
        if let Some(value) = self.hderef(curr).value {
            self.values[value.0].as_ref()
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
    /// trie.insert(b"hello", 1);
    ///
    /// *trie.get_mut(b"hello").unwrap() = 17;
    ///
    /// assert_eq!(trie.get(b"hello"), Some(&17));
    /// ```
    pub fn get_mut<K>(&mut self, key: K) -> Option<&mut V>
    where
        K: AsRef<[u8]>,
    {
        self.get_mut_by_iter(key.as_ref())
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
    /// *trie.get_mut_by_iter(b"hel".iter().chain(b"lo")).unwrap() = 17;
    /// assert_eq!(trie.get(b"hello"), Some(&17));
    /// ```
    pub fn get_mut_by_iter<'a, K>(&mut self, key: K) -> Option<&mut V>
    where
        K: IntoIterator<Item=&'a u8>,
    {
        let mut curr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(curr).child[idx] {
                curr = next;
            } else {
                return None;
            }
        }
        if let Some(value) = self.hderef(curr).value {
            self.values[value.0].as_mut()
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
    /// assert_eq!(trie.get_or_insert(b"hello", 1), &1);
    /// ```
    pub fn get_or_insert<K>(&mut self, key: K, value: V) -> &mut V
    where
        K: AsRef<[u8]>,
    {
        self.get_or_insert_by_iter_with(key.as_ref(), ||value)
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
    /// let iter = b"hello".iter().chain(b"world");
    ///
    /// *trie.get_or_insert_by_iter(iter, 1) = 17;
    ///
    /// assert_eq!(trie.get(b"helloworld"), Some(&17));
    /// ```
    pub fn get_or_insert_by_iter<'a, K>(&mut self, key: K, value: V) -> &mut V
    where
        K: IntoIterator<Item=&'a u8>,
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
    /// assert_eq!(trie.get_or_insert_with(b"hello", ||1), &1);
    /// ```
    ///
    pub fn get_or_insert_with<K, F>(&mut self, key: K, f: F) -> &mut V
    where
        K: AsRef<[u8]>,
        F: FnOnce() -> V,
    {
        self.get_or_insert_by_iter_with(key.as_ref(), f)
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
    /// let iter = b"hello".iter().chain(b"world");
    ///
    /// *trie.get_or_insert_by_iter_with(iter, ||1) = 17;
    ///
    /// assert_eq!(trie.get(b"helloworld"), Some(&17));
    /// ```
    pub fn get_or_insert_by_iter_with<'a, K, F>(&mut self, key: K, f: F)
        -> &mut V
    where
        K: IntoIterator<Item=&'a u8>,
        F: FnOnce() -> V,
    {
        let mut hcurr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(hcurr).child[idx] {
                hcurr = next;
            } else {
                let hnew = self.new_node();
                let curr = self.hderef_mut(hcurr);
                curr.child[idx] = Some(hnew);
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

    /// Inserts a value into the trie at the given key.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert(b"hello", 1);
    ///
    /// assert_eq!(trie.get(b"hello"), Some(&1));
    /// ```
    pub fn insert<K>(&mut self, key: K, value: V)
    where
        K: AsRef<[u8]>,
    {
        self.insert_by_iter(key.as_ref(), value)
    }

    /// Inserts a value into the trie at the given key. The trait bound on `K`
    /// makes it easy to pass an iterator or other type that can be converted
    /// into an iterator as a paramter.
    ///
    pub fn insert_by_iter<'a, K>(&mut self, key: K, value: V)
    where
        K: IntoIterator<Item=&'a u8>,
    {
        let mut hcurr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(hnext) = self.hderef(hcurr).child[idx] {
                hcurr = hnext;
            } else {
                let hnew = self.new_node();
                let curr = self.hderef_mut(hcurr);
                curr.child[idx] = Some(hnew);
                curr.len += 1;
                hcurr = hnew;
            }
        }
        let hvalue = self.new_value(value);
        self.hderef_mut(hcurr).value = Some(hvalue);
    }

    /// Returns an iterator over the key-value pairs in the trie.
    /// ```
    /// use trie_map::TrieMap;
    ///
    /// let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
    ///
    /// trie.insert(b"hello", 1);
    /// trie.insert(b"world", 2);
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
    /// trie.insert(b"hello", 1);
    /// trie.insert(b"world", 2);
    ///
    /// let mut iter  = trie.iter_mut();
    /// let     first = iter.next().unwrap();
    /// *first.1 = 17;
    ///
    /// assert_eq!(trie.get(b"hello"), Some(&17));
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
    /// trie.insert(b"hello", 1);
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
    /// trie.insert(b"hello", 1);
    ///
    /// assert_eq!(trie.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Removes a value from the trie at the given key, if it exists, and
    /// returns it, otherwise `None` is returned.
    ///
    pub fn remove<K>(&mut self, key: K) -> Option<V>
    where
        K: AsRef<[u8]>,
    {
        self.remove_by_iter(key.as_ref())
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
    /// trie.insert(b"hello", 1);
    ///
    /// assert_eq!(trie.remove_by_iter(b"hello"), Some(1));
    /// ```
    pub fn remove_by_iter<'a, K>(&mut self, key: K) -> Option<V>
    where
        K: IntoIterator<Item=&'a u8>,
    {
        let mut hcurr = self.root;
        let mut stack = Vec::new();
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(hcurr).child[idx] {
                stack.push((hcurr, idx));
                hcurr = next;
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
                while let Some((hnode, idx)) = stack.pop() {
                    let node = self.hderef_mut(hnode);
                    node.child[idx] = None;
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
        if let Some(handle) = self.value_bin.pop() {
            self.values[handle.0] = Some(value);
            handle
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
    fn hderef(&self, handle: NodeHandle) -> &Node<RANGE> {
        &self.nodes[handle.0]
    }

    /// Used internally to dereference a node handle mutably.
    ///
    #[inline(always)]
    fn hderef_mut(&mut self, handle: NodeHandle) -> &mut Node<RANGE> {
        &mut self.nodes[handle.0]
    }
}

impl<V, const R: usize, const B: u8> Default for TrieMap<V, R, B> {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(dead_code)]
enum IterItem<'a, V, const R: usize, const B: u8> {
    RefItem((Box<[u8]>, &'a V)),
    RefMutItem((Box<[u8]>, &'a mut V)),
    OwnedItem((Box<[u8]>, V)),
    None
}

#[allow(dead_code)]
trait InnerIter<V, const R: usize, const B: u8> {
    type Item;

    fn stack(&mut self) -> &mut Vec<(NodeHandle, usize, bool)>;
    
    fn key(&mut self) -> &mut Vec<u8>;
    
    fn values(&self) -> &Vec<Option<V>>;
    
    fn hderef(&self, handle: NodeHandle) -> &Node<R>;
    
    fn iter_item<'a>(&'a mut self, 
                     hval : ValueHandle,
                     key  : Box<[u8]>  ) -> Option<Self::Item>;

    fn inner_next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.stack().last_mut() {
            if next.1 == usize::MAX {
                next.1 = 0;
            }
        }
        while let Some((handle, mut i, _b)) = self.stack().pop() {
            if self.hderef(handle).value.is_some() && i == 0 {
                self.stack().push((handle, 0, false));
                let hval  = self.hderef(handle).value.unwrap();
                let key   = self.key().clone().into_boxed_slice();
                return self.iter_item(hval, key)
            }
            while i < R && self.hderef(handle).child[i].is_none() {
                i += 1;
            }
            if i < R {
                let child = self.hderef(handle).child[i].unwrap();
                self.key().push(i as u8 + B);
                self.stack().push((handle, i + 1, false));
                self.stack().push((child, 0, true));
            } else {
                self.key().pop();
            }
        }
        None
    }
    fn inner_next_back(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.stack().last_mut() {
            if next.1 == usize::MAX {
                next.1 = R;
            }
        }
        while let Some((handle, mut i, _b)) = self.stack().pop() {
            while i > 0 && self.hderef(handle).child[i - 1].is_none() {
                i -= 1;
            }
            if i > 0 {
                let child = self.hderef(handle).child[i - 1].unwrap();
                self.key().push(i as u8 + B - 1);
                self.stack().push((handle, i - 1, true));
                self.stack().push((child, R, true));
            } else if self.hderef(handle).value.is_some() {
                let hval  = self.hderef(handle).value.unwrap();
                let key   = self.key().clone().into_boxed_slice();
                return self.iter_item(hval, key)
            } else {
                self.key().pop();
            }
        }
        None
    }
}

pub struct IntoIter<V, const R: usize, const B: u8> {
    trie  : TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}
impl<V, const R: usize, const B: u8> IntoIter<V, R, B> {
    fn new(trie: TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, usize::MAX, true)];
        Self { trie, key: Vec::new(), stack }
    }
}

impl<V, const R: usize, const B: u8> InnerIter<V, R, B> for IntoIter<V, R, B> {
    type Item = (Box<[u8]>, V);

    fn stack(&mut self) -> &mut Vec<(NodeHandle, usize, bool)> {
        &mut self.stack
    }
    fn key(&mut self) -> &mut Vec<u8> {
        &mut self.key
    }
    fn values(&self) -> &Vec<Option<V>> {
        &self.trie.values
    }
    fn hderef(&self, handle: NodeHandle) -> &Node<R> {
        self.trie.hderef(handle)
    }
    fn iter_item<'a>(&'a mut self, 
                     hval : ValueHandle,
                     key  : Box<[u8]>  ) -> Option<Self::Item> {
        //self.trie.values[hval.0] = None;
        Some((key, self.trie.values[hval.0].take().unwrap()))
    }
}

impl<V, const R: usize, const B: u8> Iterator for IntoIter<V, R, B> {
    type Item = (Box<[u8]>, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_next()
    }
}

impl<V, const R: usize, const B: u8> DoubleEndedIterator for IntoIter<V, R, B> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner_next_back()
    }
}

/*
impl<V, const R: usize, const B: u8> Iterator for IntoIter<V, R, B> {
    type Item = (Box<[u8]>, V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.stack.last_mut() {
            if next.1 == usize::MAX {
                next.1 = 0;
            }
        }
        while let Some((handle, mut i, _b)) = self.stack.pop() {
            if self.trie.hderef(handle).value.is_some() && i == 0 {
                self.stack.push((handle, 0, false));
                let hval  = self.trie.hderef_mut(handle).value.take().unwrap();
                let value = self.trie.values[hval.0].take().unwrap();
                let key   = self.key.clone().into_boxed_slice();
                return Some((key, value));
            }
            while i < R && self.trie.hderef(handle).child[i].is_none() {
                i += 1;
            }
            if i < R {
                let child = self.trie.hderef(handle).child[i].unwrap();
                self.key.push(i as u8 + B);
                self.stack.push((handle, i + 1, false));
                self.stack.push((child, 0, true));
            } else {
                self.key.pop();
            }
        }
        None
    }
}

impl<V, const R: usize, const B: u8>
    DoubleEndedIterator for IntoIter<V, R, B>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.stack.last_mut() {
            if next.1 == usize::MAX {
                next.1 = R;
            }
        }
        while let Some((handle, mut i, _b)) = self.stack.pop() {
            while i > 0 && self.trie.hderef(handle).child[i - 1].is_none() {
                i -= 1;
            }
            if i > 0 {
                let child = self.trie.hderef(handle).child[i - 1].unwrap();
                self.key.push(i as u8 + B - 1);
                self.stack.push((handle, i - 1, true));
                self.stack.push((child, R, true));
            } else if self.trie.hderef(handle).value.is_some() {
                let hval  = self.trie.hderef_mut(handle).value.take().unwrap();
                let value = self.trie.values[hval.0].take().unwrap();
                let key   = self.key.clone().into_boxed_slice();
                self.key.pop();
                return Some((key, value));
            } else {
                self.key.pop();
            }
        }
        None
    }
}
*/

impl<V, const R: usize, const B: u8> IntoIterator for TrieMap<V, R, B> {
    type Item = (Box<[u8]>, V);
    type IntoIter = IntoIter<V, R, B>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

pub struct Iter<'a, V, const R: usize, const B: u8> {
    trie  : &'a TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}
impl<'a, V, const R: usize, const B: u8> Iter<'a, V, R, B> {
    fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, usize::MAX, true)];
        Self { trie, key: Vec::new(), stack }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for Iter<'a, V, R, B> {
    type Item = (Box<[u8]>, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.stack.last_mut() {
            if next.1 == usize::MAX {
                next.1 = 0;
            }
        }
        while let Some((handle, mut i, b)) = self.stack.pop() {
            if self.trie.hderef(handle).value.is_some() && b {
                self.stack.push((handle, 0, false));
                let hval  = self.trie.hderef(handle).value.as_ref().unwrap();
                let value = self.trie.values[hval.0].as_ref().unwrap();
                let key   = self.key.clone().into_boxed_slice();
                return Some((key, value));
            }
            while i < R && self.trie.hderef(handle).child[i].is_none() {
                i += 1;
            }
            if i < R {
                let child = self.trie.hderef(handle).child[i].unwrap();
                self.key.push(i as u8 + B);
                self.stack.push((handle, i + 1, false));
                self.stack.push((child, 0, true));
            } else {
                self.key.pop();
            }
        }
        None
    }
}

impl<'a, V, const R: usize, const B: u8>
    DoubleEndedIterator for Iter<'a, V, R, B>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.stack.last_mut() {
            if next.1 == usize::MAX {
                next.1 = R;
            }
        }
        while let Some((handle, mut i, b)) = self.stack.pop() {
            while i > 0 && self.trie.hderef(handle).child[i - 1].is_none() {
                i -= 1;
            }
            if i > 0 {
                let child = self.trie.hderef(handle).child[i - 1].unwrap();
                self.key.push(i as u8 + B - 1);
                self.stack.push((handle, i - 1, true));
                self.stack.push((child, R, true));
            } else if self.trie.hderef(handle).value.is_some() && b {
                let hval  = self.trie.hderef(handle).value.as_ref().unwrap();
                let value = self.trie.values[hval.0].as_ref().unwrap();
                let key   = self.key.clone().into_boxed_slice();
                self.key.pop();
                return Some((key, value));
            } else {
                self.key.pop();
            }
        }
        None
    }
}

impl<'a, V, const R: usize, const B: u8> IntoIterator for &'a TrieMap<V, R, B> {
    type Item = (Box<[u8]>, &'a V);
    type IntoIter = Iter<'a, V, R, B>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

pub struct IterMut<'a, V, const R: usize, const B: u8> {
    trie  : &'a mut TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}

impl<'a, V, const R: usize, const B: u8> IterMut<'a, V, R, B> {
    fn new(trie: &'a mut TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, usize::MAX, true)];
        Self { trie, key: Vec::new(), stack }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for IterMut<'a, V, R, B> {
    type Item = (Box<[u8]>, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        use std::mem::transmute;
        if let Some(next) = self.stack.last_mut() {
            if next.1 == usize::MAX {
                next.1 = 0;
            }
        }
        while let Some((hnode, mut i, b)) = self.stack.pop() {
            if self.trie.hderef(hnode).value.is_some() && b {
                self.stack.push((hnode, 0, false));
                let hval  = self.trie.hderef(hnode).value.unwrap();
                let value = self.trie.values[hval.0].as_mut().unwrap();
                let value = unsafe { transmute::<&mut V, &'a mut V>(value) };
                let key   = self.key.clone().into_boxed_slice();
                return Some((key, value));
            }
            while i < R && self.trie.hderef(hnode).child[i].is_none() {
                i += 1;
            }
            if i < R {
                let child = self.trie.hderef(hnode).child[i].unwrap();
                self.key.push(i as u8 + B);
                self.stack.push((hnode, i + 1, false));
                self.stack.push((child, 0, true));
            } else {
                self.key.pop();
            }
        }
        None
    }
}

impl<'a, V, const R: usize, const B: u8>
    DoubleEndedIterator for IterMut<'a, V, R, B>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        use std::mem::transmute;
        if let Some(next) = self.stack.last_mut() {
            if next.1 == usize::MAX {
                next.1 = R;
            }
        }
        while let Some((handle, mut i, b)) = self.stack.pop() {
            while i > 0 && self.trie.hderef(handle).child[i - 1].is_none() {
                i -= 1;
            }
            if i > 0 {
                let child = self.trie.hderef(handle).child[i - 1].unwrap();
                self.key.push(i as u8 + B - 1);
                self.stack.push((handle, i - 1, true));
                self.stack.push((child, R, true));
            } else if self.trie.hderef(handle).value.is_some() && b {
                let hval  = self.trie.hderef(handle).value.unwrap();
                let value = self.trie.values[hval.0].as_mut().unwrap();
                let value = unsafe { transmute::<&mut V, &'a mut V>(value) };
                let key   = self.key.clone().into_boxed_slice();
                self.key.pop();
                return Some((key, value));
            } else {
                self.key.pop();
            }
        }
        None
    }
}

impl <'a, V, const R: usize, const B: u8> IntoIterator
    for &'a mut TrieMap<V, R, B>
{
    type Item = (Box<[u8]>, &'a mut V);
    type IntoIter = IterMut<'a, V, R, B>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut::new(self)
    }
}

pub struct Keys<'a, V, const R: usize, const B: u8> {
    iter: Iter<'a, V, R, B>,
}

impl<'a, V, const R: usize, const B: u8> Keys<'a, V, R, B> {
    fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        Self { iter: Iter::new(trie) }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for Keys<'a, V, R, B> {
    type Item = Box<[u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(key, _)| key)
    }
}

pub struct Values<'a, V, const R: usize, const B: u8> {
    trie  : &'a TrieMap<V, R, B>,
    idx   : usize,
    count : usize,
}
impl<'a, V, const R: usize, const B: u8> Values<'a, V, R, B> {
    fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        Self { trie, idx: 0, count: trie.len() }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for Values<'a, V, R, B> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count == 0 {
            return None;
        }
        while self.idx < self.trie.values.len()
            && self.trie.values[self.idx].is_none() {
            self.idx += 1;
        }
        if self.idx < self.trie.values.len() {
            self.count -= 1;
            self.idx += 1;
            self.trie.values[self.idx - 1].as_ref()
        } else {
            None
        }
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    fn bx(slice: &[u8]) -> Box<[u8]> {
        slice.to_vec().into_boxed_slice()
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
    fn into_iter() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        let mut iter = trie.into_iter();

        assert_eq!(iter.next(), Some((bx(b"hello"), 1)));
        assert_eq!(iter.next(), Some((bx(b"world"), 2)));
        assert_eq!(iter.next(), None);

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);
        trie.insert(b"hellowalterjack", 3);

        let mut iter = trie.into_iter();

        assert_eq!(iter.next(), Some((bx(b"hello"), 1)));
        assert_eq!(iter.next(), Some((bx(b"hellowalterjack"), 3)));
        assert_eq!(iter.next(), Some((bx(b"world"), 2)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn into_iter_rev() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        let mut iter = trie.into_iter();

        assert_eq!(iter.next_back(), Some((bx(b"world"), 2)));
        assert_eq!(iter.next_back(), Some((bx(b"hello"), 1)));
        assert_eq!(iter.next_back(), None);

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);
        trie.insert(b"hellowalterjack", 3);

        let mut iter = trie.into_iter().rev();

        assert_eq!(iter.next(), Some((bx(b"world"), 2)));
        assert_eq!(iter.next(), Some((bx(b"hellowalterjack"), 3)));
        assert_eq!(iter.next(), Some((bx(b"hello"), 1)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [(b"hello", 1), (b"world", 2)];

        for (key, val) in &data {
            trie.insert(key, *val);
        }
        for ((key1, &val1), (key2, val2)) in trie.iter().zip(data) {
            assert_eq!(key1.as_ref(), key2);
            assert_eq!(val1, val2);
        }

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [("hello", 1), ("hellowalterjack", 2), ("world", 3)];

        for &(key, val) in &data {
            trie.insert(key, val);
        }
        for ((key1, &val1), (key2, val2)) in trie.iter().zip(data) {
            assert_eq!(key1.as_ref(), key2.as_bytes());
            assert_eq!(val1, val2);
        }
    }

    #[test]
    fn iter_rev() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        let mut iter = trie.iter();

        assert_eq!(iter.next_back(), Some((bx(b"world"), &2)));
        assert_eq!(iter.next_back(), Some((bx(b"hello"), &1)));
        assert_eq!(iter.next_back(), None);

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);
        trie.insert(b"hellowalterjack", 3);

        let mut iter = trie.iter().rev();

        assert_eq!(iter.next(), Some((bx(b"world"), &2)));
        assert_eq!(iter.next(), Some((bx(b"hellowalterjack"), &3)));
        assert_eq!(iter.next(), Some((bx(b"hello"), &1)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [(b"hello", 1), (b"world", 2)];

        for (key, val) in &data {
            trie.insert(key, *val);
        }
        for ((key1, val1), (key2, val2)) in trie.iter_mut().zip(data) {
            assert_eq!(key1.as_ref(), key2);
            assert_eq!(*val1, val2);
            *val1 = 17;
        }
        for ((key1, &val1), (key2, _val2)) in trie.iter().zip(data) {
            assert_eq!(key1.as_ref(), key2);
            assert_eq!(val1, 17);
        }

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [("hello", 1), ("hellowalterjack", 2), ("world", 3)];

        for &(key, val) in &data {
            trie.insert(key, val);
        }
        for ((key1, val1), (key2, val2)) in trie.iter_mut().zip(data) {
            assert_eq!(key1.as_ref(), key2.as_bytes());
            assert_eq!(*val1, val2);
            *val1 = 17;
        }
        for ((key1, &val1), (key2, _val2)) in trie.iter().zip(data) {
            assert_eq!(key1.as_ref(), key2.as_bytes());
            assert_eq!(val1, 17);
        }
    }

    #[test]
    fn iter_mut_rev() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [(b"hello", 1), (b"world", 2)];

        for (key, val) in &data {
            trie.insert(key, *val);
        }
        let iter = trie.iter_mut().rev().zip(data.into_iter().rev());

        for ((key1, val1), (key2, val2)) in iter {
            assert_eq!(key1.as_ref(), key2);
            assert_eq!(*val1, val2);
            *val1 = 17;
        }
        for ((key1, &val1), (key2, _val2)) in trie.iter().zip(data) {
            assert_eq!(key1.as_ref(), key2);
            assert_eq!(val1, 17);
        }

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [("hello", 1), ("hellowalterjack", 2), ("world", 3)];

        for &(key, val) in &data {
            trie.insert(key, val);
        }
        let iter = trie.iter_mut().rev().zip(data.into_iter().rev());

        for ((key1, val1), (key2, val2)) in iter {
            assert_eq!(key1.as_ref(), key2.as_bytes());
            assert_eq!(*val1, val2);
            *val1 = 17;
        }
        for ((key1, &val1), (key2, _val2)) in trie.iter().zip(data) {
            assert_eq!(key1.as_ref(), key2.as_bytes());
            assert_eq!(val1, 17);
        }
    }

    #[test]
    fn keys() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [(b"hello", 1), (b"world", 2)];

        for (key, val) in &data {
            trie.insert(key, *val);
        }
        for (key1, key2) in trie.keys().zip(data.iter().map(|(k, _)| k)) {
            assert_eq!(key1.as_ref(), *key2);
        }

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        let data = [("hello", 1), ("hellowalterjack", 2), ("world", 3)];

        for &(key, val) in &data {
            trie.insert(key, val);
        }
        let iter = trie.keys().zip(data.iter().map(|(k, _)| k.as_bytes()));

        for (key1, key2) in iter {
            assert_eq!(key1.as_ref(), key2);
        }
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
