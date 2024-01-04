//! # Iterators, The Iterators Used in TrieMap
//! 
//! Each iterator implements the InnerIter trait, which provides the traversal
//! algorithms. 
//! 

use crate::trie_map::*;

/// The common trait all iterators share. It provides the traversal algorithms
/// while the iterators themselves implement its accessor methods and provide
/// a stack and key vector. The Iterator and DoubleEndedIterator traits are
/// implemented by the iterators themselves, which only call the traversal
/// algorithms of this trait.
/// 
trait InnerIter<V, const R: usize, const B: u8> {
    type Item;

    /// Returns a stack used to track where in the trie the iterator is.
    /// 
    fn stack(&mut self) -> &mut Vec<(NodeHandle, usize, bool)>;
    
    /// Returns a vector used to assemble the keys during traversal.
    /// 
    fn key(&mut self) -> &mut Vec<u8>;
    
    /// Invokes the iterator's trie's hderef method.
    /// 
    fn hderef(&self, handle: NodeHandle) -> &Node<R>;

    /// Invoked on the iterator to get it to produce the next iterator item.
    /// 
    fn item(&mut self, 
            hcurr : NodeHandle,
            hval  : ValueHandle,
            key   : Box<[u8]>  ) -> Option<Self::Item>;

    /// The core of the traversal algorithm. This method is invoked by the
    /// iterator's next method. Each iterator implements Iterator and its 
    /// next() method which onlly calls this method.
    /// 
    fn inner_next(&mut self) -> Option<Self::Item> {
        if self.stack().is_empty() {
            self.stack().push((ROOT_HANDLE, 0, true))
        }
        while let Some((hcurr, mut ichild, b)) = self.stack().pop() {
            let curr = self.hderef(hcurr);
            if curr.value.is_some() && b {
                let hval  = curr.value.unwrap();
                let key   = self.key().clone().into_boxed_slice();
                self.stack().push((hcurr, 0, false));
                return self.item(hcurr, hval, key)
            }
            while ichild < R && curr.child[ichild].is_none() {
                ichild += 1;
            }
            if ichild < R {
                let hchild = curr.child[ichild].unwrap();
                self.key().push(ichild as u8 + B);
                self.stack().push((hcurr, ichild + 1, false));
                self.stack().push((hchild, 0, true));
            } else {
                self.key().pop();
            }
        }
        None
    }

    /// The core of the reverse traversal algorithm. This method is invoked by 
    /// the iterator's next_back method. Each iterator implements 
    /// DoubleEndedIterator and its next_back() method which onlly calls this 
    /// method.
    /// 
    fn inner_next_back(&mut self) -> Option<Self::Item> {
        if self.stack().is_empty() {
            self.stack().push((ROOT_HANDLE, R, true));
        }
        while let Some((hcurr, mut ichild, b)) = self.stack().pop() {
            let curr = self.hderef(hcurr);
            while ichild > 0 && curr.child[ichild - 1].is_none() {
                ichild -= 1;
            }
            if ichild > 0 {
                let hchild = curr.child[ichild - 1].unwrap();
                self.key().push(ichild as u8 + B - 1);
                self.stack().push((hcurr, ichild - 1, true));
                self.stack().push((hchild, R, true));
            } else if curr.value.is_some() && b {
                let hval  = curr.value.unwrap();
                let key   = self.key().clone().into_boxed_slice();
                self.key().pop();
                return self.item(hcurr, hval, key)
            } else {
                self.key().pop();
            }
        }
        None
    }
}

/// A consuming iterator over the key-value pairs of a `TrieMap`.
/// 
pub struct IntoIter<V, const R: usize, const B: u8> {
    trie  : TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}
impl<V, const R: usize, const B: u8> IntoIter<V, R, B> {
    pub(crate) fn new(trie: TrieMap<V, R, B>) -> Self {
        Self { trie, key: Vec::new(), stack: Vec::new() }
    }
}

impl<V, const R: usize, const B: u8> InnerIter<V, R, B> for IntoIter<V, R, B> {
    type Item = (Box<[u8]>, V);

    #[inline]
    fn stack(&mut self) -> &mut Vec<(NodeHandle, usize, bool)> {
        &mut self.stack
    }
    #[inline]
    fn key(&mut self) -> &mut Vec<u8> {
        &mut self.key
    }
    #[inline]
    fn hderef(&self, handle: NodeHandle) -> &Node<R> {
        self.trie.hderef(handle)
    }
    #[inline]
    fn item(&mut self, 
            hcurr : NodeHandle,
            hval  : ValueHandle,
            key   : Box<[u8]>  ) -> Option<Self::Item> {
        self.trie.nodes[hcurr.0].value = None;
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

impl<V, const R: usize, const B: u8> IntoIterator for TrieMap<V, R, B> {
    type Item = (Box<[u8]>, V);
    type IntoIter = IntoIter<V, R, B>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

/// An iterator over the key-value pairs of a `TrieMap` that holds an 
/// immutable reference to the trie.
/// 
pub struct Iter<'a, V, const R: usize, const B: u8> {
    trie  : &'a TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}
impl<'a, V, const R: usize, const B: u8> Iter<'a, V, R, B> {
    pub(crate) fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        Self { trie, key: Vec::new(), stack: Vec::new() }
    }
}

impl<'a, V, const R: usize, const B: u8> 
    InnerIter<V, R, B> for Iter<'a, V, R, B> 
{
    type Item = (Box<[u8]>, &'a V);

    #[inline]
    fn stack(&mut self) -> &mut Vec<(NodeHandle, usize, bool)> {
        &mut self.stack
    }
    #[inline]
    fn key(&mut self) -> &mut Vec<u8> {
        &mut self.key
    }
    #[inline]
    fn hderef(&self, handle: NodeHandle) -> &Node<R> {
        self.trie.hderef(handle)
    }
    #[inline]
    fn item(&mut self, 
            _hcurr : NodeHandle,
            hval   : ValueHandle,
            key    : Box<[u8]>  ) -> Option<Self::Item> {
        let value = self.trie.values[hval.0].as_ref().unwrap();
        Some((key, value))
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for Iter<'a, V, R, B> {
    type Item = (Box<[u8]>, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_next()
    }
}

impl<'a, V, const R: usize, const B: u8>
    DoubleEndedIterator for Iter<'a, V, R, B>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner_next_back()
    }
}

impl<'a, V, const R: usize, const B: u8> IntoIterator for &'a TrieMap<V, R, B> {
    type Item = (Box<[u8]>, &'a V);
    type IntoIter = Iter<'a, V, R, B>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

/// An iterator over the key-value pairs of a `TrieMap` that holds a mutable
/// reference to the trie. It produces items that can be modified by the caller.
/// 
pub struct IterMut<'a, V, const R: usize, const B: u8> {
    trie  : &'a mut TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}

impl<'a, V, const R: usize, const B: u8> IterMut<'a, V, R, B> {
    pub(crate) fn new(trie: &'a mut TrieMap<V, R, B>) -> Self {
        Self { trie, key: Vec::new(), stack: Vec::new() }
    }
}

impl<'a, V, const R: usize, const B: u8> 
    InnerIter<V, R, B> for IterMut<'a, V, R, B> 
{
    type Item = (Box<[u8]>, &'a mut V);

    #[inline]
    fn stack(&mut self) -> &mut Vec<(NodeHandle, usize, bool)> {
        &mut self.stack
    }
    #[inline]
    fn key(&mut self) -> &mut Vec<u8> {
        &mut self.key
    }
    #[inline]
    fn hderef(&self, handle: NodeHandle) -> &Node<R> {
        self.trie.hderef(handle)
    }
    #[inline]
    fn item<'b>(&'b mut self, 
                _hcurr : NodeHandle,
                hval   : ValueHandle,
                key    : Box<[u8]>  ) -> Option<Self::Item> {
        use std::mem::transmute;
        let value = self.trie.values[hval.0].as_mut().unwrap();
        let value = unsafe { transmute::<&mut V, &'a mut V>(value) };
        Some((key, value))
    }
}


impl<'a, V, const R: usize, const B: u8> Iterator for IterMut<'a, V, R, B> {
    type Item = (Box<[u8]>, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_next()
    }
}

impl<'a, V, const R: usize, const B: u8>
    DoubleEndedIterator for IterMut<'a, V, R, B>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner_next_back()
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

/// An iterator over the keys of a `TrieMap` that holds an immutable reference
/// to the trie.
/// 
pub struct Keys<'a, V, const R: usize, const B: u8> {
    iter: Iter<'a, V, R, B>,
}

impl<'a, V, const R: usize, const B: u8> Keys<'a, V, R, B> {
    pub(crate) fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        Self { iter: Iter::new(trie) }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for Keys<'a, V, R, B> {
    type Item = Box<[u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(key, _)| key)
    }
}

impl<'a, V, const R: usize, const B: u8> 
    DoubleEndedIterator for Keys<'a, V, R, B> 
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(key, _)| key)
    }
}

/// An iterator over the values of a `TrieMap` that holds an immutable reference
/// to the trie.
/// 
pub struct Values<'a, V, const R: usize, const B: u8> {
    iter: Iter<'a, V, R, B>,
}

impl<'a, V, const R: usize, const B: u8> Values<'a, V, R, B> {
    pub(crate) fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        Self { iter: Iter::new(trie) }
    }
}

impl<'a, V, const R: usize, const B: u8> Iterator for Values<'a, V, R, B> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_, val)| val)
    }
}

impl<'a, V, const R: usize, const B: u8> 
    DoubleEndedIterator for Values<'a, V, R, B> 
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(_, val)| val)
    }
}

impl<V, const R: usize, const B: u8, K> 
    FromIterator<(K, V)> for TrieMap<V, R, B> 
where
    K: AsRef<[u8]>,
{
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> Self {
        let mut trie = Self::new();
        for (key, value) in iter {
            trie.insert(key, value);
        }
        trie
    }
}


#[cfg(test)]
mod tests {
    use std::error::Error;

    use super::*;

    fn bx(slice: &[u8]) -> Box<[u8]> {
        slice.to_vec().into_boxed_slice()
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
    fn sorting() {
        let mut words = ["engineering", "physics", "elephant", "economics", 
                         "psychology", "anthropology", "language", "biology", 
                         "kinematics", "linguistics", "geography", "computer", 
                         "oceanography", "programming", "architecture", 
                         "astronomy", "history", "quantum", "sociology", 
                         "journalism", "democracy", "chemistry", "zoology", 
                         "mathematics", "javascript", "philosophy", 
                         "literature", "python", "nutrition", "metaphysics"];

        let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

        for (i, word) in words.iter().enumerate() {
            trie.insert(word, i as i32);
        }
        words.sort();

        let mut words = words.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        
        let sort1 = trie.keys().map(|b| Ok(String::from_utf8(b.to_vec())?))
                        .collect::<Result<Vec<_>, Box<dyn Error>>>()
                        .unwrap();

        assert_eq!(sort1, words);

        let sort2 = trie.keys().rev()
                        .map(|b| Ok(String::from_utf8(b.to_vec())?))
                        .collect::<Result<Vec<_>, Box<dyn Error>>>()
                        .unwrap();

        words.sort_by(|a, b| b.cmp(a));

        assert_eq!(sort2, words);
    }

    #[test]
    fn from_iter() {
        let trie: TrieMap<u32, 26, b'a'> = vec![
            ("foo", 1),
            ("bar", 2),
            ("baz", 3),
        ].into_iter().collect();
        assert_eq!(trie.get("bar"), Some(&2));
        assert_eq!(trie.get("baz"), Some(&3));
        assert_eq!(trie.get("foo"), Some(&1));
    }
}
