
# AA-Tree

Purely functional implementation of a balanced search tree implemented with a
2-3 tree variant, the AA-Tree.

References :

  * Balanced Search Trees Made Simple, Arne Andersson, 1993
  * Simple Balanced Binary Search Trees, Prabhakar Ragde, 2014

Package also provides adaptations to use AA-Trees as finite mappings or multi-sets.


-----------------------------------------------------------------------------


Tree API :
  * data : Tree a
    * Functor
    * Foldable

  * empty    : Tree a
  * tree     : Nat -> a -> Tree a -> Tree a -> Tree a
  * isEmpty  : Tree a -> Bool
  * order    : Tree a -> Nat
  * find     : (Ord a) => a -> Tree a -> Maybe a
  * member   : (Ord a) => a -> Tree a -> Bool
  * insert   : (Ord a) => a -> Tree a -> Tree a
  * delete   : (Ord a) => a -> Tree a -> Tree a
  * toList   : Tree a -> List a
  * fromList : Ord a => List a -> Tree a


Map API :
  * data : Map a b
    * Show

  * empty     : Map a b
  * isEmpty   : Map a b -> Bool
  * order     : Map a b -> Nat
  * find      : Ord a => a -> Map a b -> Maybe b
  * bind      : Ord a => a -> b -> Map a b -> Map a b
  * delete    : Ord a => a -> Map a b -> Map a b
  * toList    : Map a b -> List (KVPair a b)
  * fromList  : (Ord a) => List (KVPair a b) -> Map a b
  * keyList   : Map a b -> List a
  * valueList : Map a b -> List b
  * foldr     : (f : KVPair a b -> acc -> acc) -> acc -> Map a b -> acc


Set API :



