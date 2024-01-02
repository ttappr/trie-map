//! # TrieMap, A Trie-based Map for Rust
//! 
//! Like a HashMap, values are stored and accessible by keys. Lookups can be 
//! much faster than a HashMap, but there are some limitations on what can be 
//! used for a key, and the memory is potentially higher, but not always.
//! 
//! The keys are u8 bytes and the base value and range can be specified. The
//! greater the range, the more memory is used per node. The base value is used
//! to adjust the byte values of the keys to serve as indices into the internal
//! arrays within nodes that hold handles to descendant nodes. The base value 
//! must be less than the range. It is up to the user to ensure that the base 
//! value and range are appropriate for the keys that will be used.
//! 
//! Because the keys are bytes, they can be used to store strings, but they can
//! also be used to store any other sequence of bytes. The keys are not
//! required to be valid UTF-8.
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
/// it will have a value of None. The `brats` array is used to reference the 
/// next descendant nodes indexed by the byte value of the next character in 
/// the key.
/// 
/// `RANGE` controls the size of the `brats` array. The larger the `RANGE`, the
/// larger the array, the more characters that can be used in keys, however at
/// the cost of some more memory usage.
/// 
struct Node<const RANGE: usize> {
    brats : [Option<NodeHandle>; RANGE],
    value : Option<ValueHandle>,
}
impl<const RANGE: usize> Node<RANGE> {
    fn new() -> Self {
        Self { brats: [None; RANGE], value: None }
    }
}

/// A trie-based Map keyed on sequences of byts with values stored at the leaves
/// of the trie. `RANGE` controls the size of the `brats` array in each node.
/// And `BASE_CHAR` is the byte value of the first character in the range of
/// characters that can be used in keys. It is used to adjust each character in 
/// a key to serve as indices into the their descendant arrays.
///  
pub struct TrieMap<V, const RANGE: usize, const BASE_CHAR: u8> {
    root   : NodeHandle,
    nodes  : Vec<Node<RANGE>>,
    values : Vec<Option<V>>,
}
impl<V, const RANGE: usize, const BASE_CHAR: u8> TrieMap<V, RANGE, BASE_CHAR> {
    /// Creates a new empty trie.
    /// 
    pub fn new() -> Self {
        Self { 
            root   : NodeHandle(0), 
            nodes  : vec![Node::new()], 
            values : vec![],
        }
    }

    /// Creates a new empty trie with the given capacity. Only the internal
    /// vector that holds the values is affected by this method.
    /// 
    pub fn with_capacity(capacity: usize) -> Self {
        Self { 
            root   : NodeHandle(0), 
            nodes  : vec![Node::new()], 
            values : Vec::with_capacity(capacity),
        }
    }

    /// Inserts a value into the trie at the given key.
    /// 
    pub fn insert<'a, K>(&mut self, key: K, value: V) 
    where
        K: IntoIterator<Item = &'a u8>,
    {
        let mut curr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(curr).brats[idx] {
                curr = next;
            } else {
                let next = self.new_node();
                self.hderef_mut(curr).brats[idx] = Some(next);
                curr = next;
            }
        }
        self.values.push(Some(value));
        self.hderef_mut(curr).value = Some(ValueHandle(self.values.len() - 1));
    }

    /// Accesses a value in the trie at the given key, if it exists, a reference
    /// is returned, otherwise `None` is returned.
    /// 
    pub fn get<'a, K>(&self, key: K) -> Option<&V> 
    where
        K: IntoIterator<Item = &'a u8>,
    {
        let mut curr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(curr).brats[idx] {
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
    /// 
    pub fn get_mut<'a, K>(&mut self, key: K) -> Option<&mut V> 
    where
        K: IntoIterator<Item = &'a u8>,
    {
        let mut curr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(curr).brats[idx] {
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
    /// 
    pub fn get_or_insert<'a, K>(&mut self, key: K, value: V) -> &mut V 
    where
        K: IntoIterator<Item = &'a u8>,
    {
        self.get_or_insert_with(key, ||value)
    }

    /// Returns a mutable reference to a value in the trie at the given key, if
    /// it exists, otherwise the given function is called to produce a value
    /// which is inserted and a reference to it is returned.
    /// 
    pub fn get_or_insert_with<'a, K, F>(&mut self, key: K, f: F) -> &mut V 
    where
        K: IntoIterator<Item = &'a u8>,
        F: FnOnce() -> V,
    {
        let mut curr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(curr).brats[idx] {
                curr = next;
            } else {
                let next = self.new_node();
                self.hderef_mut(curr).brats[idx] = Some(next);
                curr = next;
            }
        }
        let handle = {
            if let Some(handle) = self.hderef(curr).value {
                handle
            } else {
                let handle = ValueHandle(self.values.len());
                self.values.push(Some(f()));
                self.hderef_mut(curr).value = Some(handle);
                handle
            }
        };
        self.values[handle.0].as_mut().unwrap()
    }

    /// Returns `true` if the trie contains a value at the given key, otherwise
    /// `false` is returned.
    /// 
    pub fn contains<'a, K>(&self, key: K) -> bool 
    where
        K: IntoIterator<Item = &'a u8>,
    {
        let mut curr = self.root;
        for b in key {
            let idx = (b - BASE_CHAR) as usize;
            if let Some(next) = self.hderef(curr).brats[idx] {
                curr = next;
            } else {
                return false;
            }
        }
        self.hderef(curr).value.is_some()
    }

    /// Returns an iterator over the key-value pairs in the trie.
    /// 
    pub fn iter(&self) -> KeyValueIter<V, RANGE, BASE_CHAR> {
        KeyValueIter::new(self)
    }

    /// Returns an iterator over the values in the trie.
    /// 
    pub fn values(&self) -> ValuesIter<V, RANGE, BASE_CHAR> {
        ValuesIter::new(self)
    }

    /// Returns an iterator over the keys in the trie.
    /// 
    pub fn keys(&self) -> KeysIter<V, RANGE, BASE_CHAR> {
        KeysIter::new(self)
    }

    /// Used internally to create a new node and return a handle to it.
    /// 
    fn new_node(&mut self) -> NodeHandle {
        self.nodes.push(Node::new());
        NodeHandle(self.nodes.len() - 1)
    }

    /// Used internally to dereference a node handle.
    /// 
    fn hderef(&self, handle: NodeHandle) -> &Node<RANGE> {
        &self.nodes[handle.0]
    }

    /// Used internally to dereference a node handle mutably.
    /// 
    fn hderef_mut(&mut self, handle: NodeHandle) -> &mut Node<RANGE> {
        &mut self.nodes[handle.0]
    }
}

impl<V, const R: usize, const B: u8> Default for TrieMap<V, R, B> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct KeyValueIterator<V, const R: usize, const B: u8> {
    trie  : TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize)>,
}
impl<V, const R: usize, const B: u8> KeyValueIterator<V, R, B> {
    fn new(trie: TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, 0)];
        Self { trie, key: Vec::new(), stack }
    }
}

impl<V, const R: usize, const B: u8> Iterator for KeyValueIterator<V, R, B> {
    type Item = (Vec<u8>, V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((handle, mut i)) = self.stack.pop() {
            if self.trie.hderef(handle).value.is_some() && i == 0 {
                self.stack.push((handle, 0));
                let hval  = self.trie.hderef_mut(handle).value.take().unwrap();
                let value = self.trie.values[hval.0].take().unwrap();
                return Some((self.key.clone(), value));
            }
            while i < R && self.trie.hderef(handle).brats[i].is_none() {
                i += 1;
            }
            if i < R {
                let brat = self.trie.hderef(handle).brats[i].unwrap();
                self.key.push(i as u8 + B);
                self.stack.push((handle, i + 1));
                self.stack.push((brat, 0));
            } else {
                self.key.pop();
            }
        }
        None
    }
}

impl<V, const R: usize, const B: u8> IntoIterator for TrieMap<V, R, B> {
    type Item = (Vec<u8>, V);
    type IntoIter = KeyValueIterator<V, R, B>;

    fn into_iter(self) -> Self::IntoIter {
        KeyValueIterator::new(self)
    }
}

pub struct KeyValueIter<'a, V, const R: usize, const B: u8> {
    trie  : &'a TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}
impl<'a, V, const R: usize, const B: u8> KeyValueIter<'a, V, R, B> {
    fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, 0, true)];
        Self { trie, key: Vec::new(), stack }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator 
    for KeyValueIter<'a, V, R, B> 
{
    type Item = (Box<[u8]>, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((handle, mut i, b)) = self.stack.pop() {
            if self.trie.hderef(handle).value.is_some() && b {
                self.stack.push((handle, 0, false));
                let hval  = self.trie.hderef(handle).value.as_ref().unwrap();
                let value = self.trie.values[hval.0].as_ref().unwrap();
                let key   = self.key.clone().into_boxed_slice();
                return Some((key, value));
            }
            while i < R && self.trie.hderef(handle).brats[i].is_none() {
                i += 1;
            }
            if i < R {
                let brat = self.trie.hderef(handle).brats[i].unwrap();
                self.key.push(i as u8 + B);
                self.stack.push((handle, i + 1, false));
                self.stack.push((brat, 0, true));
            } else {
                self.key.pop();
            }
        }
        None
    }
}

impl<'a, V, const R: usize, const B: u8> IntoIterator 
    for &'a TrieMap<V, R, B> 
{
    type Item = (Box<[u8]>, &'a V);
    type IntoIter = KeyValueIter<'a, V, R, B>;

    fn into_iter(self) -> Self::IntoIter {
        KeyValueIter::new(self)
    }
}

pub struct KeysIter<'a, V, const R: usize, const B: u8> {
    trie  : &'a TrieMap<V, R, B>,
    stack : Vec<(NodeHandle, usize, bool)>,
    key   : Vec<u8>,
}

impl<'a, V, const R: usize, const B: u8> KeysIter<'a, V, R, B> {
    fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, 0, true)];
        Self { trie, key: Vec::new(), stack }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for KeysIter<'a, V, R, B> {
    type Item = Box<[u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((handle, mut i, b)) = self.stack.pop() {
            if self.trie.hderef(handle).value.is_some() && b {
                self.stack.push((handle, 0, false));
                return Some(self.key.clone().into_boxed_slice());
            }
            while i < R && self.trie.hderef(handle).brats[i].is_none() {
                i += 1;
            }
            if i < R {
                let brat = self.trie.hderef(handle).brats[i].unwrap();
                self.key.push(i as u8 + B);
                self.stack.push((handle, i + 1, false));
                self.stack.push((brat, 0, true));
            } else {
                self.key.pop();
            }
        }
        None
    }
}

pub struct ValuesIter<'a, V, const R: usize, const B: u8> {
    trie  : &'a TrieMap<V, R, B>,
    idx   : usize,
}
impl<'a, V, const R: usize, const B: u8> ValuesIter<'a, V, R, B> {
    fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        Self { trie, idx: 0 }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for ValuesIter<'a, V, R, B> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.idx += 1;
        self.trie.values[self.idx - 1].as_ref()
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn into_iter() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        let mut iter = trie.into_iter();

        assert_eq!(iter.next(), Some((b"hello".to_vec(), 1)));
        assert_eq!(iter.next(), Some((b"world".to_vec(), 2)));
        assert_eq!(iter.next(), None);

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);
        trie.insert(b"hellowalterjack", 3);

        let mut iter = trie.into_iter();

        assert_eq!(iter.next(), Some((b"hello".to_vec(), 1)));
        assert_eq!(iter.next(), Some((b"hellowalterjack".to_vec(), 3)));
        assert_eq!(iter.next(), Some((b"world".to_vec(), 2)));
        assert_eq!(iter.next(), None);
    }

    #[test] 
    fn iter() {
        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();
        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);

        let mut iter = trie.iter();
        
        let item1 = iter.next().unwrap();
        let item2 = iter.next().unwrap();

        assert_eq!(&*item1.0, b"hello");
        assert_eq!(item1.1, &1);

        assert_eq!(&*item2.0, b"world");
        assert_eq!(item2.1, &2);

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        trie.insert(b"hello", 1);
        trie.insert(b"world", 2);
        trie.insert(b"hellowalterjack", 3);

        let mut iter = trie.iter();

        let item1 = iter.next().unwrap();
        let item2 = iter.next().unwrap();
        let item3 = iter.next().unwrap();

        assert_eq!(&*item1.0, b"hello");
        assert_eq!(item1.1, &1);

        assert_eq!(&*item2.0, b"hellowalterjack");
        assert_eq!(item2.1, &3);

        assert_eq!(&*item3.0, b"world");
        assert_eq!(item3.1, &2);
    }
}