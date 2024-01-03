use crate::trie_map::*;

trait InnerIter<V, const R: usize, const B: u8> {
    type Item;

    fn stack(&mut self) -> &mut Vec<(NodeHandle, usize, bool)>;
    
    fn key(&mut self) -> &mut Vec<u8>;
    
    fn values(&self) -> &Vec<Option<V>>;
    
    fn hderef(&self, handle: NodeHandle) -> &Node<R>;
    
    fn iter_item<'a>(&'a mut self, 
                     hcurr : NodeHandle,
                     hval  : ValueHandle,
                     key   : Box<[u8]>  ) -> Option<Self::Item>;

    fn inner_next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.stack().last_mut() {
            if next.1 == usize::MAX {
                next.1 = 0;
            }
        }
        while let Some((hcurr, mut i, b)) = self.stack().pop() {
            if self.hderef(hcurr).value.is_some() && b {
                self.stack().push((hcurr, 0, false));
                let hval  = self.hderef(hcurr).value.unwrap();
                let key   = self.key().clone().into_boxed_slice();
                return self.iter_item(hcurr, hval, key)
            }
            while i < R && self.hderef(hcurr).child[i].is_none() {
                i += 1;
            }
            if i < R {
                let child = self.hderef(hcurr).child[i].unwrap();
                self.key().push(i as u8 + B);
                self.stack().push((hcurr, i + 1, false));
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
        while let Some((hcurr, mut i, b)) = self.stack().pop() {
            while i > 0 && self.hderef(hcurr).child[i - 1].is_none() {
                i -= 1;
            }
            if i > 0 {
                let child = self.hderef(hcurr).child[i - 1].unwrap();
                self.key().push(i as u8 + B - 1);
                self.stack().push((hcurr, i - 1, true));
                self.stack().push((child, R, true));
            } else if self.hderef(hcurr).value.is_some() && b {
                let hval  = self.hderef(hcurr).value.unwrap();
                let key   = self.key().clone().into_boxed_slice();
                self.key().pop();
                return self.iter_item(hcurr, hval, key)
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
    pub(crate) fn new(trie: TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, usize::MAX, true)];
        Self { trie, key: Vec::new(), stack }
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
    fn values(&self) -> &Vec<Option<V>> {
        &self.trie.values
    }
    #[inline]
    fn hderef(&self, handle: NodeHandle) -> &Node<R> {
        self.trie.hderef(handle)
    }
    #[inline]
    fn iter_item<'a>(&'a mut self, 
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

pub struct Iter<'a, V, const R: usize, const B: u8> {
    trie  : &'a TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}
impl<'a, V, const R: usize, const B: u8> Iter<'a, V, R, B> {
    pub(crate) fn new(trie: &'a TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, usize::MAX, true)];
        Self { trie, key: Vec::new(), stack }
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
    fn values(&self) -> &Vec<Option<V>> {
        &self.trie.values
    }
    #[inline]
    fn hderef(&self, handle: NodeHandle) -> &Node<R> {
        self.trie.hderef(handle)
    }
    #[inline]
    fn iter_item<'b>(&'b mut self, 
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

pub struct IterMut<'a, V, const R: usize, const B: u8> {
    trie  : &'a mut TrieMap<V, R, B>,
    key   : Vec<u8>,
    stack : Vec<(NodeHandle, usize, bool)>,
}

impl<'a, V, const R: usize, const B: u8> IterMut<'a, V, R, B> {
    pub(crate) fn new(trie: &'a mut TrieMap<V, R, B>) -> Self {
        let curr  = trie.root;
        let stack = vec![(curr, usize::MAX, true)];
        Self { trie, key: Vec::new(), stack }
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
    fn values(&self) -> &Vec<Option<V>> {
        &self.trie.values
    }
    #[inline]
    fn hderef(&self, handle: NodeHandle) -> &Node<R> {
        self.trie.hderef(handle)
    }
    #[inline]
    fn iter_item<'b>(&'b mut self, 
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

pub struct Values<'a, V, const R: usize, const B: u8> {
    trie  : &'a TrieMap<V, R, B>,
    idx   : usize,
    count : usize,
}
impl<'a, V, const R: usize, const B: u8> Values<'a, V, R, B> {
    pub(crate) fn new(trie: &'a TrieMap<V, R, B>) -> Self {
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
