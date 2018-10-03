
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

module Data.AA.Map

import Data.AA.Tree

%default total
%access private

--}

----------------------------------------------------------------------------------------[ KV Pair ]
--{1

||| Key Value pair to use as tree leaf nodes.
public export
data KVPair : Type -> Type -> Type where
  KV : k -> v -> KVPair k v


||| Equality for Key-Value pairs.
export
(Eq k) => Eq (KVPair k v) where
  (==) (KV k1 _) (KV k2 _) = k1 == k2


||| Partial Ordering for Key-Value pairs.
export
(Ord k) => Ord (KVPair k v) where
  compare (KV k1 _) (KV k2 _) = compare k1 k2


||| Represent Key-Value pairs as a String.
export
(Show k, Show v) => Show (KVPair k v) where
  show (KV k v) = "{ " ++  show k ++ " : " ++ show v ++ " }"

--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

||| Use an AATree of Key-Value pairs as a Finite Map.
export
data Map : Type -> Type -> Type where
  M : Tree (KVPair a b) -> Map a b

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
  where go : Ord a => Tree (KVPair a b) -> Maybe b
        go t with (t)
          | E                = Nothing
          | T _ (KV k v) l r = case compare x k of
                                 LT => go l
                                 EQ => Just v
                                 GT => go r

||| Bind a value to a given key. If it already exists, overwrite the old value.
export
bind : Ord a => a -> b -> Map a b -> Map a b
bind k v (M t) = M $ insert (KV k v) t

||| Delete a node from the finite mapping that matches a key.
export
delete : Ord a => a -> Map a b -> Map a b
delete x (M t) = go t
  where go : Ord a => Tree (KVPair a b) -> Map a b
        go t with (t)
          | E                = M E
          -- We do not care what v is, so just use the first one as a dummy
          -- value in AA.delete.
          | T _ (KV k v) l r = M $ Tree.delete (KV x v) t


||| Convert a list of Key-Value tuples to a finite mapping.
export
toList : Map a b -> List (KVPair a b)
toList (M t) = Tree.toList t

||| Convert a finite mapping to a list of Key-Value tuples.
export
fromList : (Ord a) => List (a,b) -> Map a b
fromList lst = M $ foldr (\(k,v),t => insert (KV k v) t) empty lst

||| Return a list of all Keys present in a KV-Tree.
export
keyList : Map a b -> List a
keyList m = map (\(KV k v) => k) $ toList m

||| Return a list of all Values present in a KV-Tree.
export
valueList : Map a b -> List b
valueList m = map (\(KV k v) => v) $ toList m

||| Just like regular foldr, but f is fixed to 'KVPair a b' domain.
export
foldr : (f : KVPair a b -> acc -> acc) -> acc -> Map a b -> acc
foldr f acc (M t) = foldr f acc t


||| String representation of a KV-Tree finite mapping.
export
(Show (KVPair a b)) => Show (Map a b) where
  show m = case toList m of
                  []  => "[]"
                  [x] => "[ " ++ show x ++ " ]"
                  xs  => "[ " ++ (go xs) ++ "\n]"
  where
    go : List (KVPair a b) -> String
    go lst = case lst of
               []      => ""
               [x]     => show x
               (x::xs) => show x ++ "\n, " ++ (go xs)

--}


