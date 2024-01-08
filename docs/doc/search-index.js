var searchIndex = JSON.parse('{\
"trie_map":{"doc":"","t":"DDALLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLALLLLLLLLLLLLLLLLLLDDLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLALLLLLLLLLLLLLLLLLAADDDDDDLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLDDLLLLLLLLLLLLLLLLLLLLAADDDDDDLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLDDLLLLLLLLLLLLLLLLLLLL","n":["TrieMap","TrieSet","base16","borrow","borrow","borrow_mut","borrow_mut","clear","clear","contains","contains_by_iter","contains_by_iter","contains_key","default","default","fmt","fmt","from","from","from_iter","get","get_by_iter","get_mut","get_mut_by_iter","get_or_insert","get_or_insert_by_iter","get_or_insert_by_iter_with","get_or_insert_with","insert","insert","insert_by_iter","insert_by_iter","into","into","into_iter","into_iter","into_iter","into_iter","into_iter","is_empty","is_empty","iter","iter","iter_mut","iterators","keys","len","len","new","new","remove","remove","remove_by_iter","remove_by_iter","try_from","try_from","try_into","try_into","type_id","type_id","values","values_mut","with_capacity","TrieMapBase16","TrieSetBase16","borrow","borrow","borrow_mut","borrow_mut","clear","clear","contains","contains_by_iter","contains_key","contains_key_by_iter","default","fmt","fmt","from","from","get","get_by_iter","get_mut","get_mut_by_iter","get_or_insert","get_or_insert_by_iter","get_or_insert_by_iter_with","get_or_insert_with","insert","insert","insert_by_iter","into","into","into_iter","into_iter","into_iter","into_iter","into_iter","is_empty","is_empty","iter","iter","iter_mut","iterators","keys","len","len","new","new","remove","remove","remove_by_iter","remove_by_iter","try_from","try_from","try_into","try_into","type_id","type_id","values","values_mut","trie_map_base16","trie_set_base16","IntoIter","Iter","IterMut","Keys","Values","ValuesMut","borrow","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","from","from","from","from","from","from","into","into","into","into","into","into","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","next","next","next","next","next","next","next_back","next_back","next_back","next_back","next_back","next_back","try_from","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","type_id","IntoIter","Iter","borrow","borrow","borrow_mut","borrow_mut","from","from","into","into","into_iter","into_iter","next","next","next_back","next_back","try_from","try_from","try_into","try_into","type_id","type_id","trie_map","trie_set","IntoIter","Iter","IterMut","Keys","Values","ValuesMut","borrow","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","from","from","from","from","from","from","into","into","into","into","into","into","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","next","next","next","next","next","next","next_back","next_back","next_back","next_back","next_back","next_back","try_from","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","type_id","IntoIter","Iter","borrow","borrow","borrow_mut","borrow_mut","from","from","into","into","into_iter","into_iter","next","next","next_back","next_back","try_from","try_from","try_into","try_into","type_id","type_id"],"q":[[0,"trie_map"],[63,"trie_map::base16"],[121,"trie_map::base16::iterators"],[123,"trie_map::base16::iterators::trie_map_base16"],[189,"trie_map::base16::iterators::trie_set_base16"],[211,"trie_map::iterators"],[213,"trie_map::iterators::trie_map"],[279,"trie_map::iterators::trie_set"],[301,"core::convert"],[302,"core::iter::traits::iterator"],[303,"core::fmt"],[304,"core::fmt"],[305,"core::option"],[306,"core::ops::function"],[307,"core::result"],[308,"core::any"],[309,"core::borrow"]],"d":["A trie-based Map keyed on sequences of bytes with values …","A set implemented using TrieMap. Internally this is a …","This module provides the <code>TrieMapBase16</code> and <code>TrieSetBase16</code> …","","","","","Clears the trie, removing all values.","Removes all elements from the set.","Reports whether the set contains the given key.","Returns <code>true</code> if the trie contains a value at the given …","Reports whether the set contains the given key. The key is …","Returns <code>true</code> if the trie contains a value at the given …","","","","","Returns the argument unchanged.","Returns the argument unchanged.","","Accesses a value in the trie at the given key, if it …","Accesses a value in the trie at the given key, if it …","Returns a mutable reference to a value in the trie at the …","Returns a mutable reference to a value in the trie at the …","Returns a mutable reference to a value in the trie at the …","Returns a mutable reference to a value in the trie at the …","Returns a mutable reference to a value in the trie at the …","Returns a mutable reference to a value in the trie at the …","Inserts a value into the trie at the given key. If the key …","Inserts the given key into the set. Returns true if the …","Inserts a value into the trie at the given key. The trait …","Inserts the given key into the set. Returns true if the …","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","Returns <code>true</code> if the trie contains no values, otherwise …","Returns true if the set contains no elements.","Returns an iterator over the key-value pairs in the trie.","Returns an iterator over the keys of the set.","Returns an iterator over the mutable key-value pairs in …","","Returns an iterator over the keys in the trie.","Returns the number of values in the trie.","Returns the number of elements in the set.","Creates a new empty trie.","Creates a new empty TrieSet.","Removes a value from the trie at the given key, if it …","Removes the given key from the set. Returns true if the …","Removes a value from the trie at the given key, if it …","Removes the given key from the set. Returns true if the …","","","","","","","Returns an iterator over the values in the trie.","Returns an iterator over the values in the trie.","Creates a new empty trie with the given capacity. Only the …","A trie whose keys can be any string with no restrictions …","A set implemented as a trie that encodes its keys as base …","","","","","Removes all key-value pairs from the map.","Removes all elements from the set.","Reports whether the set contains the given key.","Reports whether the set contains the given key. The key is …","Returns <code>true</code> if the map contains a value for the specified …","Returns <code>true</code> if the map contains a value for the specified …","","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns a reference to the value corresponding to the key, …","Returns a reference to the value corresponding to the key, …","Returns a mutable reference to the value corresponding to …","Returns a mutable reference to the value corresponding to …","If the key-value pair is not present in the map, inserts …","If the key-value pair is not present in the map, inserts …","If the key-value pair is not present in the map, inserts …","If the key-value pair is not present in the map, inserts …","Inserts a key-value pair into the map. If the key already …","Inserts the given key into the set. Returns true if the …","Inserts the given key into the set. Returns true if the …","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","Returns <code>true</code> if the map contains no key-value pairs.","Reports whether the set is empty.","Returns an iterator over the key-value pairs of the map in …","Returns an iterator over the set.","Returns an iterator over the key-value pairs of the map. …","","Returns an iterator over the keys of the map in canonical …","Returns the number of key-value pairs in the map.","Returns an iterator over the set.","Creates an empty <code>TrieMapBase16</code>.","Creates a new empty TrieSet.","Removes a key from the map, returning the value at the key …","Removes the given key from the set. Returns true if the …","Removes a key from the map, returning the value at the key …","Removes the given key from the set. Returns true if the …","","","","","","","Returns an iterator over the values of the map. They will …","Returns an iterator over the values of the map. They will …","","","","","","","","","","","","","","","","","","","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","An owning iterator over the elements of a TrieSet.","An iterator over the elements of a TrieSet.","","","","","Returns the argument unchanged.","Returns the argument unchanged.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","","","","","","","A consuming iterator over the key-value pairs of a <code>TrieMap</code>.","An iterator over the key-value pairs of a <code>TrieMap</code> that …","An iterator over the key-value pairs of a <code>TrieMap</code> that …","An iterator over the keys of a <code>TrieMap</code> that holds an …","An iterator over the values of a <code>TrieMap</code> that holds an …","","","","","","","","","","","","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Returns the argument unchanged.","Returns the argument unchanged.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","","","",""],"i":[0,0,0,1,3,1,3,1,3,3,1,3,1,1,3,1,3,1,3,1,1,1,1,1,1,1,1,1,1,3,1,3,1,3,1,1,1,3,3,1,3,1,3,1,0,1,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,1,1,0,0,24,25,24,25,24,25,25,25,24,24,25,24,25,24,25,24,24,24,24,24,24,24,24,24,25,25,24,25,24,24,24,25,25,24,25,24,25,24,0,24,24,25,24,25,24,25,24,25,24,25,24,25,24,25,24,24,0,0,0,0,0,0,0,0,34,28,30,31,32,33,34,28,30,31,32,33,34,28,30,31,32,33,34,28,30,31,32,33,34,28,30,31,32,33,34,28,30,31,32,33,34,28,30,31,32,33,34,28,30,31,32,33,34,28,30,31,32,33,34,28,30,31,32,33,0,0,29,35,29,35,29,35,29,35,29,35,29,35,29,35,29,35,29,35,29,35,0,0,0,0,0,0,0,0,36,15,17,18,22,23,36,15,17,18,22,23,36,15,17,18,22,23,36,15,17,18,22,23,36,15,17,18,22,23,36,15,17,18,22,23,36,15,17,18,22,23,36,15,17,18,22,23,36,15,17,18,22,23,36,15,17,18,22,23,0,0,37,16,37,16,37,16,37,16,37,16,37,16,37,16,37,16,37,16,37,16],"f":[0,0,0,[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[1,[-1]]],2,[]],[3,2],[[3,-1],4,[[7,[[6,[5]]]]]],[[[1,[-1]],-2],4,[],8],[[3,-1],4,8],[[[1,[-1]],-2],4,[],[[7,[[6,[5]]]]]],[[],[[1,[-1]]],[]],[[],3],[[[1,[-1]],9],10,11],[[3,9],10],[-1,-1,[]],[-1,-1,[]],[-1,[[1,[-2]]],12,[]],[[[1,[-1]],-2],[[13,[-1]]],[],[[7,[[6,[5]]]]]],[[[1,[-1]],-2],[[13,[-1]]],[],8],[[[1,[-1]],-2],[[13,[-1]]],[],[[7,[[6,[5]]]]]],[[[1,[-1]],-2],[[13,[-1]]],[],8],[[[1,[-1]],-2,-1],-1,[],[[7,[[6,[5]]]]]],[[[1,[-1]],-2,-1],-1,[],8],[[[1,[-1]],-2,-3],-1,[],8,14],[[[1,[-1]],-2,-3],-1,[],[[7,[[6,[5]]]]],14],[[[1,[-1]],-2,-1],[[13,[-1]]],[],[[7,[[6,[5]]]]]],[[3,-1],4,[[7,[[6,[5]]]]]],[[[1,[-1]],-2,-1],[[13,[-1]]],[],8],[[3,-1],4,8],[-1,-2,[],[]],[-1,-2,[],[]],[[[1,[-1]]],[],[]],[[[1,[-1]]],[],[]],[[[1,[-1]]],[],[]],[3],[3],[[[1,[-1]]],4,[]],[3,4],[[[1,[-1]]],[[15,[-1]]],[]],[3,16],[[[1,[-1]]],[[17,[-1]]],[]],0,[[[1,[-1]]],[[18,[-1]]],[]],[[[1,[-1]]],19,[]],[3,19],[[],[[1,[-1]]],[]],[[],3],[[[1,[-1]],-2],[[13,[-1]]],[],[[7,[[6,[5]]]]]],[[3,-1],4,[[7,[[6,[5]]]]]],[[[1,[-1]],-2],[[13,[-1]]],[],8],[[3,-1],4,8],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,21,[]],[-1,21,[]],[[[1,[-1]]],[[22,[-1]]],[]],[[[1,[-1]]],[[23,[-1]]],[]],[19,[[1,[-1]]],[]],0,0,[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[24,[-1]]],2,[]],[25,2],[[25,26],4],[[25,-1],4,8],[[[24,[-1]],26],4,[]],[[[24,[-1]],-2],4,[],8],[[],25],[[[24,[-1]],9],10,11],[[25,9],10],[-1,-1,[]],[-1,-1,[]],[[[24,[-1]],26],[[13,[-1]]],[]],[[[24,[-1]],-2],[[13,[-1]]],[],8],[[[24,[-1]],26],[[13,[-1]]],[]],[[[24,[-1]],-2],[[13,[-1]]],[],8],[[[24,[-1]],-2,-1],-1,[],[[27,[26]]]],[[[24,[-1]],-2,-1],-1,[],8],[[[24,[-1]],-2,-3],-1,[],8,14],[[[24,[-1]],-2,-3],-1,[],[[27,[26]]],14],[[[24,[-1]],-2,-1],[[13,[-1]]],[],[[27,[26]]]],[[25,-1],4,[[27,[26]]]],[[25,-1],4,8],[-1,-2,[],[]],[-1,-2,[],[]],[[[24,[-1]]],[],[]],[[[24,[-1]]],[],[]],[[[24,[-1]]],[],[]],[25],[25],[[[24,[-1]]],4,[]],[25,4],[[[24,[-1]]],[[28,[-1]]],[]],[25,29],[[[24,[-1]]],[[30,[-1]]],[]],0,[[[24,[-1]]],[[31,[-1]]],[]],[[[24,[-1]]],19,[]],[25,19],[[],[[24,[-1]]],[]],[[],25],[[[24,[-1]],26],[[13,[-1]]],[]],[[25,26],4],[[[24,[-1]],-2],[[13,[-1]]],[],8],[[25,-1],4,8],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,21,[]],[-1,21,[]],[[[24,[-1]]],[[32,[-1]]],[]],[[[24,[-1]]],[[33,[-1]]],[]],0,0,0,0,0,0,0,0,[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[34,[-1]]],13,[]],[[[28,[-1]]],13,[]],[[[30,[-1]]],13,[]],[[[31,[-1]]],13,[]],[[[32,[-1]]],13,[]],[[[33,[-1]]],13,[]],[[[34,[-1]]],13,[]],[[[28,[-1]]],13,[]],[[[30,[-1]]],13,[]],[[[31,[-1]]],13,[]],[[[32,[-1]]],13,[]],[[[33,[-1]]],13,[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,21,[]],[-1,21,[]],[-1,21,[]],[-1,21,[]],[-1,21,[]],[-1,21,[]],0,0,[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-1,[]],[-1,-1,[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[29,13],[35,13],[29,13],[35,13],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,21,[]],[-1,21,[]],0,0,0,0,0,0,0,0,[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[36,[-1]]],13,[]],[[[15,[-1]]],13,[]],[[[17,[-1]]],13,[]],[[[18,[-1]]],13,[]],[[[22,[-1]]],13,[]],[[[23,[-1]]],13,[]],[[[36,[-1]]],13,[]],[[[15,[-1]]],13,[]],[[[17,[-1]]],13,[]],[[[18,[-1]]],13,[]],[[[22,[-1]]],13,[]],[[[23,[-1]]],13,[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,21,[]],[-1,21,[]],[-1,21,[]],[-1,21,[]],[-1,21,[]],[-1,21,[]],0,0,[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-1,[]],[-1,-1,[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[37,13],[16,13],[37,13],[16,13],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,[[20,[-2]]],[],[]],[-1,21,[]],[-1,21,[]]],"c":[],"p":[[3,"TrieMap",0],[15,"tuple"],[3,"TrieSet",0],[15,"bool"],[15,"u8"],[15,"slice"],[8,"AsRef",301],[8,"Iterator",302],[3,"Formatter",303],[6,"Result",303],[8,"Debug",303],[8,"IntoIterator",304],[4,"Option",305],[8,"FnOnce",306],[3,"Iter",213],[3,"Iter",279],[3,"IterMut",213],[3,"Keys",213],[15,"usize"],[4,"Result",307],[3,"TypeId",308],[3,"Values",213],[3,"ValuesMut",213],[3,"TrieMapBase16",63],[3,"TrieSetBase16",63],[15,"str"],[8,"Borrow",309],[3,"Iter",123],[3,"Iter",189],[3,"IterMut",123],[3,"Keys",123],[3,"Values",123],[3,"ValuesMut",123],[3,"IntoIter",123],[3,"IntoIter",189],[3,"IntoIter",213],[3,"IntoIter",279]],"b":[[34,"impl-IntoIterator-for-%26TrieMap%3CV,+R,+B%3E"],[35,"impl-IntoIterator-for-TrieMap%3CV,+R,+B%3E"],[36,"impl-IntoIterator-for-%26mut+TrieMap%3CV,+R,+B%3E"],[37,"impl-IntoIterator-for-%26TrieSet%3CR,+B%3E"],[38,"impl-IntoIterator-for-TrieSet%3CR,+B%3E"],[93,"impl-IntoIterator-for-TrieMapBase16%3CV%3E"],[94,"impl-IntoIterator-for-%26mut+TrieMapBase16%3CV%3E"],[95,"impl-IntoIterator-for-%26TrieMapBase16%3CV%3E"],[96,"impl-IntoIterator-for-%26TrieSetBase16"],[97,"impl-IntoIterator-for-TrieSetBase16"]]}\
}');
if (typeof window !== 'undefined' && window.initSearch) {window.initSearch(searchIndex)};
if (typeof exports !== 'undefined') {exports.searchIndex = searchIndex};
