
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED
--
-- Finite mapping using an AA-Tree of key-value tuples.

module Data.AA.Map

import Data.AA.Tree

%default total
%access private

--}

----------------------------------------------------------------------------------------[ KV Pair ]
--{1

||| Key Value pair to use as tree leaf nodes.
public export
data Cell : Type -> Type -> Type where
  Elem : k -> v -> Cell k v

export
(Eq k) => Eq (Cell k v) where
  (==) (Elem k1 _) (Elem k2 _) = k1 == k2

export
(Ord k) => Ord (Cell k v) where
  compare (Elem k1 _) (Elem k2 _) = compare k1 k2

export
(Show k, Show v) => Show (Cell k v) where
  show (Elem k v) = "{ " ++  show k ++ " : " ++ show v ++ " }"

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

||| Use an AATree of Key-Value pairs as a Finite Map.
export
data Map : Type -> Type -> Type where
  M : Tree (Cell a b) -> Map a b

--}

--------------------------------------------------------------------------------------------[ API ]
--{1

||| The empty mapping.
export
empty : Map a b
empty = M Tree.empty

||| Check if mapping is empty.
export
isEmpty : Map a b -> Bool
isEmpty (M t) = Tree.isEmpty t

||| Order of the mapping - i.e.- size
export
order : Map a b -> Nat
order (M t) = Tree.order t

||| Lookup a value in the finite mapping given a key.
export
find : Ord a => a -> Map a b -> Maybe b
find x (M t) = go t
  where go : Ord a => Tree (Cell a b) -> Maybe b
        go t with (t)
          | E                  = Nothing
          | T _ (Elem k v) l r = case compare x k of
                                   LT => go l
                                   EQ => Just v
                                   GT => go r

||| Bind a value to a given key. If it already exists, overwrite the old value.
export
bind : Ord a => a -> b -> Map a b -> Map a b
bind k v (M t) = M $ insert (Elem k v) t

||| Delete a node from the finite mapping that matches a key.
export
delete : Ord a => a -> Map a b -> Map a b
delete x (M t) = go t
  where go : Ord a => Tree (Cell a b) -> Map a b
        go t with (t)
          | E                = M E
          -- We do not care what v is, so just use the first one as a dummy
          -- value in AA.delete.
          | T _ (Elem k v) l r = M $ Tree.delete (Elem x v) t


||| Convert a list of Key-Value tuples to a finite mapping.
export
toList : Map a b -> List (Cell a b)
toList (M t) = Tree.toList t

||| Convert a finite mapping to a list of Key-Value tuples.
export
fromList : (Ord a) => List (a,b) -> Map a b
fromList lst = M $ foldr (\(k,v),t => insert (Elem k v) t) empty lst

||| Return a list of all Keys present in a Elem-Tree.
export
keyList : Map a b -> List a
keyList m = map (\(Elem k v) => k) $ toList m

||| Return a list of all Values present in a Elem-Tree.
export
valueList : Map a b -> List b
valueList m = map (\(Elem k v) => v) $ toList m

||| Just like regular foldr, but f is fixed to 'Cell a b' domain.
export
foldr : (f : Cell a b -> acc -> acc) -> acc -> Map a b -> acc
foldr f acc (M t) = foldr f acc t


||| String representation of a Elem-Tree finite mapping.
export
(Show (Cell a b)) => Show (Map a b) where
  show m = case toList m of
                  []  => "[]"
                  [x] => "[ " ++ show x ++ " ]"
                  xs  => "[ " ++ (go xs) ++ "\n]"
  where
    go : List (Cell a b) -> String
    go lst = case lst of
               []      => ""
               [x]     => show x
               (x::xs) => show x ++ "\n, " ++ (go xs)

--}


