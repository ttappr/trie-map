# TrieMap, A Fast, No-Frills Trie For Rust

This crate offers a very basic implementation for a trie with a focus on the
speed of insertions and access operations.

The nodes of the trie have fixed-size arrays holding handles to their 
successors. The nodes themselves are contained in contiguous memory indexed
by the handles, with the intent of leveraging data locality for cache 
efficiency. The values are likewise stored in separate continguous memory
indexed by value handles.

The size of the node arrays can be configured through the generic parameters,
`RANGE` and `BASE_CHAR`. For instance, the code below sets up a trie that
supports keys composed of the 26 lowercase ASCII characters.

``` rust
use trie_map::TrieMap;

// RANGE = 26, BASE_CHAR = b'a'.
let mut trie: TrieMap<i32, 26, b'a'> = TrieMap::new();

trie.insert("hello", 1);

assert_eq!(trie.contains("hello"), true);
```

Each node of the trie, as configured above, will have a fixed-size descendant 
array of 26 length, which are indexed into directly by the next character's byte
value minus `BASE_CHAR`.

The methods of the trie support key types of `String`, `&str`, `&[u8]`, and 
other types that implement either `AsRef<[u8]>` or `IntoIterator<Item=&u8>`.
Internally, the key's bytes are iterated over to populate the trie. These 
bytes can be UTF-8/ASCII compatible characters, or they could represent
anything suitable to a project's requirements so long as `RANGE` and
`BASE_CHAR` are correctly specified.

