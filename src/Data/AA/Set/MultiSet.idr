-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

module Data.AA.Set.MultiSet

import Data.AA.Tree

%default total
%access private

--}

------------------------------------------------------------------------------------------[ Types ]
--{1

public export
data Cell : Type -> Type where
  Elem : a -> Nat -> Cell a

export
(Eq a) => Eq (Cell a) where
  (==) (Elem x1 _) (Elem x2 _) = x1 == x2

export
(Ord a) => Ord (Cell a) where
  compare (Elem x1 _) (Elem x2 _) = compare x1 x2

export
(Show a) => Show (Cell a) where
  show (Elem x n) = concat ["{ ", show x, " : ", show n, " }"]

export
data MSet : Type -> Type where
  MS : Tree (Cell a) -> MSet a

export
(Show a) => Show (MSet a) where
  show (MS s) = "[\n" ++ (foldr (\x,r => "  " ++ show x ++ "\n" ++ r) "" s) ++ "]"

export
Functor MSet where
  map f (MS s) = MS $ (\(Elem x n) => Elem (f x) n) <$> s

export
foldr : (f : Cell a -> acc -> acc) -> acc -> MSet a -> acc
foldr f acc (MS s) = foldr f acc s

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

export
empty : MSet a
empty = MS Tree.empty


export
isEmpty : MSet a -> Bool
isEmpty (MS t) = Tree.isEmpty t


export
order : MSet a -> Nat
order = foldr (\(Elem _ n),acc =>  n + acc) 0


export
count : Ord a => a -> MSet a -> Nat
count x (MS t) = go t where
  go : Tree (Cell a) -> Nat
  go t with (t)
    | E                   = Z
    | T _ (Elem x' n) l r = case compare x x' of
                              LT => go l
                              EQ => n
                              GT => go r


export
card : Ord a => a -> MSet a -> Nat
card x (MS t) = go t where
  go : Tree (Cell a) -> Nat
  go t with (t)
    | E                   = Z
    | T _ (Elem x' n) l r = case compare x x' of
                              LT => go l
                              EQ => n
                              GT => go r


export
member : Ord a => a -> MSet a -> Bool
member x s with (card x s)
  | Z = False
  | _ = True


export
insert : Ord a => a -> MSet a -> MSet a
insert x s with (count x s)
  | Z = let MS t = s in MS $ Tree.insert (Elem x 1) t
  | n = let MS t = s in MS $ Tree.insert (Elem x (S n)) t


export
delete : Ord a => a -> MSet a -> MSet a
delete x s with (count x s)
  | Z   = s
  | S n = let MS t = s in MS $ Tree.insert (Elem x n) t


export
union : Ord a => MSet a -> MSet a -> MSet a
union (MS s) (MS t) = MS $ foldr alg s t
  where alg : Cell a -> Tree (Cell a) -> Tree (Cell a)
        alg x r with (Tree.find x r)
          | Nothing         = Tree.insert x r
          | Just (Elem _ m) = let Elem v n = x
                              in Tree.insert (Elem v (n + m)) r


export
intersect : Ord a => MSet a -> MSet a -> MSet a
intersect (MS s) t = MS $ foldr alg empty s
  where
    alg : Ord a => Cell a -> Tree (Cell a) -> Tree (Cell a)
    alg (Elem v n) r with (card v t)
      | Z = r
      | m = Tree.insert (Elem v (min n m)) r


export
filter : Ord a => (Cell a -> Bool) -> MSet a -> MSet a
filter f (MS s) = MS $ foldr (\x,s' => case f x of
                                              True  => insert x s'
                                              False => s'
                                  ) empty s

export
fromList : Ord a => List a -> MSet a
fromList = foldr (\x,r => insert x r) empty


export
elems : Ord a => MSet a -> List a
elems = foldr alg []
  where alg : Cell a -> List a -> List a
        alg (Elem x _) xs = x::xs

--}

------------------------------------------------------------------------------[ Syntax Extensions ]
--{1

syntax "#" [xs] ";" = MultiSet.fromList xs;

--}

