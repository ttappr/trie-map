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

An idea on how to define keys that could hold a large character range while 
keeping the trie nodes small: base32, or some other, encoding could be used. 
And since many of the trie's methods will take an iterator for a key, encoding a
key to perform a lookup could be done by a custom encoding iterator that will 
stop once the trie determines the lookup key is not in the trie.

``` rust
use trie_map::TrieMap;
use pictures::PicFile;
use my_encoders::Ascii27Encoder;

let mut key_encoder = Ascii27Encoder::new();
let mut trie        = TrieMap::<Picture, 27, b'`'>::new();

let picture = PicFile::load("./arctic_fox.png");

trie.insert(&key_encoder::iter_encode("Αρκτική αλεπού"), picture);

// Encoding and lookup stop immediately, since "Pallas's Cat" isn't in the trie.
assert_eq!(trie.contains_by_iter(&key_encoder.iter_encode("Pallas's Cat")), 
           false);

assert_eq!(trie.contains_by_iter(&key_encoder.iter_encode("Αρκτική αλεπού")), 
           true);
```

The above is somewhat hypothetical, but it could be a workable strategy to
keep the node sizes of the trie small while supporting an unlimited range of
characters in the keys. In the idea above, `Ascii27Encoder` converts any
characters outside the range of lowercase ASCII characters to ASCII lowercase
alpha characters escaped with a back-tick '`'. And lowercase alpha ASCII
characters are passed through unescaped as-is.