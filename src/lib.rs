
mod trie_map;
mod trie_set;

mod trie_map_base16;
mod trie_set_base16;

pub use trie_map::TrieMap;
pub use trie_set::TrieSet;
pub mod iterators;

/// This module provides the `TrieMapBase16` and `TrieSetBase16` types, which
/// are specialized versions of `TrieMap` and `TrieSet` that use base-16
/// encoding for their keys.
///
pub mod base16 {
    pub use crate::trie_map_base16::TrieMapBase16;
    pub use crate::trie_set_base16::TrieSetBase16;
    pub mod map_iterators {
        pub use crate::trie_map_base16::{
            Iter, IterMut, IntoIter, Keys, Values,
        };
    }
    pub mod set_iterators {
        pub use crate::trie_set_base16::{
            Iter, IntoIter,
        };
    }
}