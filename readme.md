## TrieMap, A Fast, No-Frills Trie For Rust

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
other types that implement `AsRef<[u8]>`; other methods take 
`Iterator<Item=u8>`. Which can be conveniently supplied by the `.bytes()` method
of `&str` or `String`. Internally, the key's bytes are iterated over to populate
the trie. These bytes can be UTF-8/ASCII compatible characters, or they could 
represent anything suitable to a project's requirements so long as `RANGE` and
`BASE_CHAR` are correctly specified.

### Base 16 Wrappers

This crate provides `trie_map_base16::{TrieMapBase16<V>, TrieSetBase16<V>}` 
which wrap a `TrieMap<V, 16, b'a'>` instance and base16 encode its keys so 
there's no restriction on the characters in strings used as keys. Strings could 
be in Greek, or any language for that matter, and contain special characters.

`TrieMapBase16<V>` and `TrieSetBase16<V>` progressively encode the keys passed 
to them, so in cases where an operation such as `get()` is being performed and 
the key is not in the trie, it will fail early only having processed the minimum
number of bytes of the key necessary to determine the miss.

`TrieMapBase16<V>` demonstrates the flexibility of `TrieMap<V, R, B>` which
can be used in other specialized custom tries.

``` rust
    use trie_map::base16::TrieMapBase16;
    
    let mut trie = TrieMapBase16::new();
    
    trie.insert("Γειά σου", 1);
    trie.insert("κόσμος", 2);
    trie.insert("👋", 42);
    trie.insert("🌍", 43);
    
    assert_eq!(trie.get("Γειά σου"), Some(&1));
    assert_eq!(trie.get("κόσμος"), Some(&2));
    assert_eq!(trie.get("👋"), Some(&42));
    assert_eq!(trie.get("🌍"), Some(&43));
```
