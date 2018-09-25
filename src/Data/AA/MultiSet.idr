
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

module Data.AA.MultiSet

import Data.AA.Tree

%default total
%access private

--}

------------------------------------------------------------------------------------------[ Types ]
--{1

public export
data CPair : Type -> Type where
  Elem : a -> Nat -> CPair a

export
(Eq a) => Eq (CPair a) where
  (==) (Elem x1 _) (Elem x2 _) = x1 == x2

export
(Ord a) => Ord (CPair a) where
  compare (Elem x1 _) (Elem x2 _) = compare x1 x2

export
(Show a) => Show (CPair a) where
  show (Elem x n) = concat ["{ ", show x, " : ", show n, " }"]

export
data MultiSet : Type -> Type where
  MS : Tree (CPair a) -> MultiSet a

export
(Show a) => Show (MultiSet a) where
  show (MS s) = "[\n" ++ (foldr (\x,r => "  " ++ show x ++ "\n" ++ r) "" s) ++ "]"

export
Functor MultiSet where
  map f (MS s) = MS $ (\(Elem x n) => Elem (f x) n) <$> s

--export
--Applicative MultiSet where
--  pure  x   = MultiSet.insert x empty
--  (<*>) s t =

export
foldr : (f : CPair a -> acc -> acc) -> acc -> MultiSet a -> acc
foldr f acc (MS s) = foldr f acc s

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

export
empty : MultiSet a
empty = MS Tree.empty


export
isEmpty : MultiSet a -> Bool
isEmpty (MS t) = Tree.isEmpty t


export
order : MultiSet a -> Nat
order = foldr (\(Elem _ n),acc =>  n + acc) 0


export
count : Ord a => a -> MultiSet a -> Nat
count x (MS t) = go t where
  go : Tree (CPair a) -> Nat
  go t with (t)
    | E                   = Z
    | T _ (Elem x' n) l r = case compare x x' of
                              LT => go l
                              EQ => n
                              GT => go r


export
member : Ord a => a -> MultiSet a -> Bool
member x (MS t) = go t where
  go : Tree (CPair a) -> Bool
  go t with (t)
    | E                   = False
    | T _ (Elem x' _) l r = case compare x x' of
                              LT => go l
                              EQ => True
                              GT => go r


export
insert : Ord a => a -> MultiSet a -> MultiSet a
insert x s with (count x s)
  | Z = let MS t = s in MS $ Tree.insert (Elem x 1) t
  | n = let MS t = s in MS $ Tree.insert (Elem x (S n)) t


export
delete : Ord a => a -> MultiSet a -> MultiSet a
delete x s with (count x s)
  | Z   = s
  | S n = let MS t = s in MS $ Tree.insert (Elem x n) t


export
union : Ord a => MultiSet a -> MultiSet a -> MultiSet a
union (MS s) (MS t) = MS $ foldr (\x,r =>
  let q        = Tree.find x r
      Elem v n = x
  in case q of
       Nothing         => Tree.insert x r
       Just (Elem _ m) => Tree.insert (Elem v (n + m)) r
  ) s t


export
intersect : Ord a => MultiSet a -> MultiSet a -> MultiSet a
intersect (MS s) (MS t) = MS $ foldr (\x,r => if member x t
                                                then insert x r
                                                else r
                                     ) empty s


export
fromList : Ord a => List a -> MultiSet a
fromList = foldr (\x,r => insert x r) empty


export
elems : Ord a => MultiSet a -> List a
elems = foldr alg []
  where alg : CPair a -> List a -> List a
        alg (Elem x _) xs = x::xs

--}

------------------------------------------------------------------------------[ Syntax Extensions ]
--{1

syntax "#" [xs] ";" = MultiSet.fromList xs;

--}

