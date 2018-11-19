-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

module Data.AA.Set.NatIso

import Data.AA.Tree

%default total
%access private

%flag C "-O3"
%flag C "-g"

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

data Cell : Type -> Type where
  Elem : a -> Nat -> Cell a

Eq a => Eq (Cell a) where
  (==) (Elem x1 _) (Elem x2 _) = x1 == x2

Ord a => Ord (Cell a) where
  compare (Elem x1 n1) (Elem x2 n2) = compare x1 x2

export
data NatIso : Type -> Type where
  NI : Nat -> Tree (Cell a) -> NatIso a

export
empty : NatIso a
empty = NI Z Tree.empty

export
Functor NatIso where
  map f (NI n t) = NI n (map (\(Elem x n) => Elem (f x) n) t)

--}

--------------------------------------------------------------------------------------------[ API ]
--{1

export
find : Ord a => a -> NatIso a -> Maybe Nat
find x (NI n t) with (Tree.find (Elem x Z) t)
  | Nothing          = Nothing
  | Just (Elem _ n') = Just n'

export
insert : Ord a => a -> NatIso a -> NatIso a
insert x ni@(NI n t) = case (NatIso.find x ni) of
                         Nothing => NI (n+1) $ insert (Elem x n) t
                         Just _  => NI n t

export
toList : NatIso a -> List a
toList (NI _ t) = foldl (\acc,(Elem x _) => x :: acc) [] t

--}


