
mod trie_map;
mod trie_set;
mod trie_map_base16;
mod trie_set_base16;
mod trie_map_iterators;

pub use crate::trie_map::TrieMap;
pub use crate::trie_set::TrieSet;

/// This module contains the iterators for `TrieMap` and `TrieSet`.
/// 
pub mod iterators {
    /// This module contains the iterators for `TrieMap`.
    /// 
    pub mod trie_map {
        pub use crate::trie_map_iterators::{
            Iter, IterMut, IntoIter, Keys, Values, ValuesMut,
        };
    }

    /// This module contains the iterators for `TrieSet`.
    /// 
    pub mod trie_set {
        pub use crate::trie_set::{
            Iter, IntoIter,
        };
    }
}

/// This module contains the `TrieMapBase16` and `TrieSetBase16` types, which
/// are specialized versions of `TrieMap` and `TrieSet` that use base-16
/// encoding for their keys.
///
pub mod base16 {
    pub use crate::trie_map_base16::TrieMapBase16;
    pub use crate::trie_set_base16::TrieSetBase16;

    /// This module contains the iterators for `TrieMapBase16` and
    /// `TrieSetBase16`.
    /// 
    pub mod iterators {
        /// This module contains the iterators for `TrieMapBase16`.
        /// 
        pub mod trie_map_base16 {
            pub use crate::trie_map_base16::{
                Iter, IterMut, IntoIter, Keys, Values, ValuesMut,
            };
        }
        /// This module contains the iterators for `TrieSetBase16`.
        /// 
        pub mod trie_set_base16 {
            pub use crate::trie_set_base16::{
                Iter, IntoIter,
            };
        }
    }
}