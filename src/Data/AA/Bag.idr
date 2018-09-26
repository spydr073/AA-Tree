-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED
--
-- This module provides a data structure for indexed bins.
--

module Data.AA.Bag

import Data.AA.Tree
import Data.AA.MultiSet

%default total
%access private

--}

----------------------------------------------------------------------------------------[ KV Pair ]
--{1

||| Pair composed of an index and it's corresponding bin.
public export
data BagPair : Type -> Type -> Type where
  Bin : k -> MultiSet v -> BagPair k v


||| Equality for bag elements.
export
(Eq k) => Eq (BagPair k v) where
  (==) (Bin k1 _) (Bin k2 _) = k1 == k2


||| Partial Ordering for bag elements.
export
(Ord k) => Ord (BagPair k v) where
  compare (Bin k1 _) (Bin k2 _) = compare k1 k2


||| Represent bins as a String.
export
(Show k, Show v) => Show (BagPair k v) where
  show (Bin k v) = "{ " ++  show k ++ " : " ++ show v ++ " }"

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

||| Use an AATree of bag elements to model a bag.
export
data Bag : Type -> Type -> Type where
  B : Tree (BagPair a b) -> Bag a b

--}

--------------------------------------------------------------------------------------------[ API ]
--{1

||| The empty bag.
export
empty : Bag a b
empty = B Tree.empty

||| Check if bag is empty.
export
isEmpty : Bag a b -> Bool
isEmpty (B t) = Tree.isEmpty t

||| Order of the bag - i.e.- number of bins
export
order : Bag a b -> Nat
order (B t) = Tree.order t

||| Lookup bin contents given an index.
export
find : Ord a => a -> Bag a b -> Maybe (MultiSet b)
find x (B t) = go t
  where go : Ord a => Tree (BagPair a b) -> Maybe (MultiSet b)
        go t with (t)
          | E                = Nothing
          | T _ (Bin k v) l r = case compare x k of
                                  LT => go l
                                  EQ => Just v
                                  GT => go r

||| Insert values into a bin given an index.
export
insert : (Ord a, Ord b) => a -> MultiSet b -> Bag a b -> Bag a b
insert k v b with (find k b)
  | Nothing = let B t = b in B $ Tree.insert (Bin k v) t
  | Just v' = let B t = b in B $ Tree.insert (Bin k (union v v')) t


||| Remove a bin from the bag.
export
delete : Ord a => a -> Bag a b -> Bag a b
delete x (B t) = go t
  where go : Ord a => Tree (BagPair a b) -> Bag a b
        go t with (t)
          | E         = B E
          | T _ _ _ _ = B $ Tree.delete (Bin x empty) t


||| Convert a bag into a list of bins.
export
toList : Bag a b -> List (BagPair a b)
toList (B t) = Tree.toList t

||| Convert a list of bins into a bag.
export
fromList : (Ord a) => List (BagPair a b) -> Bag a b
fromList lst = B $ Tree.fromList lst

||| Return a list of all bin indexes.
export
binList : Bag a b -> List a
binList b = map (\(Bin k v) => k) $ toList b

||| Return a list of all bin contents.
export
setList : Bag a b -> List (MultiSet b)
setList b = map (\(Bin k v) => v) $ toList b

||| Just like regular foldr, but f is fixed to 'BagPair a b' domain.
export
foldr : (f : BagPair a b -> acc -> acc) -> acc -> Bag a b -> acc
foldr f acc (B t) = foldr f acc t


||| String representation of a bag.
export
(Show (BagPair a b)) => Show (Bag a b) where
  show b = case toList b of
                  []  => "[]"
                  [x] => "[ " ++ show x ++ " ]"
                  xs  => "[ " ++ show xs ++ "\n]"

--}


