-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED
--
-- This module provides a data structure for indexed bins of multisets.
--

module Data.AA.Set.IndexMultiSet

import Data.AA.Tree
import Data.AA.Set.MultiSet

%default total
%access private

--}

----------------------------------------------------------------------------------------[ KV Pair ]
--{1

||| Pair composed of an index and it's corresponding bin.
public export
data Cell : Type -> Type -> Type where
  Bin : k -> MSet v -> Cell k v

export
(Eq k) => Eq (Cell k v) where
  (==) (Bin k1 _) (Bin k2 _) = k1 == k2

export
(Ord k) => Ord (Cell k v) where
  compare (Bin k1 _) (Bin k2 _) = compare k1 k2

export
(Show k, Show v) => Show (Cell k v) where
  show (Bin k v) = "{ " ++  show k ++ " : " ++ show v ++ " }"

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

||| Use an AATree of bin cells to model an indexed multiset.
export
data IMSet : Type -> Type -> Type where
  B : Tree (Cell a b) -> IMSet a b

--}

--------------------------------------------------------------------------------------------[ API ]
--{1

||| The empty indexed multiset.
export
empty : IMSet a b
empty = B Tree.empty

||| Check if indexed multiset is empty.
export
isEmpty : IMSet a b -> Bool
isEmpty (B t) = Tree.isEmpty t

||| Order of the indexed multiset - i.e.- number of indexes.
export
order : IMSet a b -> Nat
order (B t) = Tree.order t

||| Lookup bin contents given an index.
export
find : Ord a => a -> IMSet a b -> Maybe (MSet b)
find x (B t) = go t
  where go : Ord a => Tree (Cell a b) -> Maybe (MSet b)
        go t with (t)
          | E                = Nothing
          | T _ (Bin k v) l r = case compare x k of
                                  LT => go l
                                  EQ => Just v
                                  GT => go r


||| Insert values into a bin given an index.
export
insert : (Ord a, Ord b) => a -> MSet b -> IMSet a b -> IMSet a b
insert k v b with (find k b)
  | Nothing = let B t = b in B $ Tree.insert (Bin k v) t
  | Just v' = let B t = b in B $ Tree.insert (Bin k (union v v')) t


||| Remove a bin from the indexed multiset.
export
delete : Ord a => a -> IMSet a b -> IMSet a b
delete x (B t) = go t
  where go : Ord a => Tree (Cell a b) -> IMSet a b
        go t with (t)
          | E         = B E
          | T _ _ _ _ = B $ Tree.delete (Bin x empty) t


||| Convert an indexed multiset into a list of bins.
export
toList : IMSet a b -> List (Cell a b)
toList (B t) = Tree.toList t

||| Convert a list of bins into an indexed multiset.
export
fromList : (Ord a) => List (Cell a b) -> IMSet a b
fromList lst = B $ Tree.fromList lst

||| Return a list of all bin indexes.
export
binList : IMSet a b -> List a
binList b = map (\(Bin k v) => k) $ toList b

||| Return a list of all bin contents.
export
setList : IMSet a b -> List (MSet b)
setList b = map (\(Bin k v) => v) $ toList b

||| Just like regular foldr, but f is fixed to 'Cell a b' domain.
export
foldr : (f : Cell a b -> acc -> acc) -> acc -> IMSet a b -> acc
foldr f acc (B t) = foldr f acc t


||| String representation of an indexd multiset.
export
(Show (Cell a b)) => Show (IMSet a b) where
  show b = case toList b of
                  []  => "[]"
                  [x] => "[ " ++ show x ++ " ]"
                  xs  => "[ " ++ show xs ++ "\n]"

--}


