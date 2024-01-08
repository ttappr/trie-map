## TrieMap, A Fast, No-Frills Trie For Rust

See [the documentation](https://ttappr.github.io/trie-map/doc/trie_map/index.html).

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

This crate provides `base16::{TrieMapBase16<V>, TrieSetBase16<V>}` 
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
    use std::collections::VecDeque;
    use std::iter::repeat;

    const WIN_LEN: usize = 20;

    let input = "ababcdjjjabxzydjjzxyababzbabajjjjj";
    let words = [("ababcd", 1), ("abxzyd", 2), 
                 ("bzbaba", 3), ("zxyaba", 4)];

    let mut window = repeat(b'_').take(WIN_LEN).collect::<VecDeque<_>>();
    let mut count  = 0;

    let trie = words.into_iter().collect::<TrieMapBase16<i32>>();

    let k = words[0].0.len();

    for b in input.bytes() {
        // Determine what word is leaving the window.
        if trie.contains_key_by_iter(window.range(..k).copied()) {
            count -= 1;
            println!("{count} words currently in the window.");
        }
        window.pop_front();
        window.push_back(b);
        
        // Determine whether a word has just entered the window.
        if trie.contains_key_by_iter(window.range(WIN_LEN - k..).copied()) {
            count += 1;
            println!("{count} words currently in the window.");
        }
    }
```
