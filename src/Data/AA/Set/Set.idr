-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED
-- Represent a Set as an AA-Tree of elements.

module Data.AA.Set.Set

import Data.AA.Tree

%default total
%access private

--}

------------------------------------------------------------------------------------------[ Types ]
--{1

||| Wrapper to use a tree of elements as a set.
export
data Set : Type -> Type where
  S : Tree a -> Set a

-- a bit ugly... change output later
export
(Show a) => Show (Set a) where
  show (S t) = "[" ++ (foldr (\x,r => show x ++ "," ++ r) "" t) ++ "]"

export
Functor Set where
  map f (S t) = S $ f <$> t

Foldable Set where
  foldr f acc (S t) = foldr f acc t

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

||| The empty multiset.
export
empty : Set a
empty = S Tree.empty


||| Predicate for empty set
export
isEmpty : Set a -> Bool
isEmpty (S t) = Tree.isEmpty t


||| The order, or 'size', of a set.
export
order : Set a -> Nat
order = foldr (\x,acc => 1 + acc) 0


||| Check if an item is a member of a given set.
export
member : Ord a => a -> Set a -> Bool
member x (S t) = Tree.member x t


||| Insert an element into a set.
export
insert : Ord a => a -> Set a -> Set a
insert x (S t) = S $ Tree.insert x t


||| Delete an element from a set.
export
delete : Ord a => a -> Set a -> Set a
delete x (S t) = S $ Tree.delete x t


||| Set union operator.
export
union : Ord a => Set a -> Set a -> Set a
union (S s) (S t) = S $ foldr alg s t
  where alg : a -> Tree a -> Tree a
        alg x r = Tree.insert x r


||| Set intersection operator.
export
intersect : Ord a => Set a -> Set a -> Set a
intersect (S s) t = S $ foldr alg empty s
  where
    alg : Ord a => a -> Tree a -> Tree a
    alg x r with (member x t)
      | False = r
      | True = Tree.insert x r

||| Set difference operator.
export
diff : Ord a => Set a -> Set a -> Set a
diff (S s) t = S $ foldr alg empty s
  where
    alg : Ord a => a -> Tree a -> Tree a
    alg x r with (member x t)
      | False = Tree.insert x r
      | True  = r


||| Filter element in a set by a given predicate.
export
filter : Ord a => (a -> Bool) -> Set a -> Set a
filter f (S s) = S $ foldr (\x,s' => case f x of
                                       True  => insert x s'
                                       False => s'
                           ) empty s


||| Convert a list into a set.
export
fromList : Ord a => List a -> Set a
fromList = foldr (\x,r => insert x r) empty


||| Get a list of all unique set elements.
export
toList : Ord a => Set a -> List a
toList = foldr alg []
  where alg : a -> List a -> List a
        alg x xs = x::xs

--}

------------------------------------------------------------------------------[ Syntax Extensions ]
--{1

syntax "#" [xs] ";" = Set.fromList xs;

--}

