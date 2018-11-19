
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED

-- Purely functional implementation of a balanced search tree implemented with a
-- 2-3 tree variant, the AA-Tree.

module Data.AA.Tree

%default total
%access private

--}

-------------------------------------------------------------------------------------------[ Core ]
--{1

||| Balanced AA-Tree data type
public export
data Tree : Type -> Type where
  ||| empty tree
  E : Tree a
  ||| non-empty sub-tree
  T : Nat -> a -> Tree a -> Tree a -> Tree a

||| Smart constructor for empty tree
export
empty : Tree a
empty = E

||| Smart constructor for non-empty tree
export
tree : Nat -> a -> Tree a -> Tree a -> Tree a
tree = T

export
Functor Tree where
  map f t with (t)
    | E         = E
    | T n k l r = T n (f k) (f <$> l) (f <$> r)

||| Fold over a tree
export
Foldable Tree where
  foldr f acc t with (t)
    | E         = acc
    | T _ k l r = foldr f (f k (foldr f acc r)) l


--}

----------------------------------------------------------------------------------------[ Prelude ]
--{1

||| Check if tree is empty
export
isEmpty : Tree a -> Bool
isEmpty t with (t)
  | E = True
  | _ = False


||| Determine the order of the tree (i.e.- number of elements)
export
order : Tree a -> Nat
order t with (t)
  | E = 0
  | T _ _ l r = 1 + (order l) + (order r)


||| Search a tree for an element
export
find : (Ord a) => a -> Tree a -> Maybe a
find x t with (t)
  | E         = Nothing
  | T _ k l r = case compare x k of
                  LT => find x l
                  EQ => Just k
                  GT => find x r


||| Check if an element is a member of a tree
export
member : (Ord a) => a -> Tree a -> Bool
member k t with (find k t)
  | Nothing = False
  | Just _  = True

-- 2-3 Tree Skew Operation :
--  x <- y          x -> y
-- / \    \   =>   /    / \
--a  b     c      a    b   c
skew : Tree a -> Tree a
skew t = case t of
           T ly y (T lx x a b) c =>
             if ly == lx
               then T lx x a (T ly y b c)
               else t
           _ => t


-- 2-3 Tree Split Operation :
--                         y
--  x -> y -> z          /   \
-- /    /    / \   =>   x     z
--a    b    c   d      / \   / \
--                    a   b c   d
split : Tree a -> Tree a
split t = case t of
            T lx x a (T ly y b (T lz z c d)) =>
              if lx == ly && ly == lz
                then T (S ly) y (T lx x a b) (T lz z c d)
                else t
            _ => t


||| Insert an element into a tree. If the element already exists, overwrite it.
export
insert : (Ord a) => a -> Tree a -> Tree a
insert x t with (t)
  | E           = T 1 x E E
  | T l k tl tr = case compare x k of
                    LT => (split . skew) $ T l k (insert x tl) tr
                    EQ => T l x tl tr
                    GT => (split . skew) $ T l k tl (insert x tr)


||| Delete an element from a tree. If the element does not exist, do nothing.
export
delete : (Ord a) => a -> Tree a -> Tree a
delete _ E = E
delete x t@(T h k l r) = case compare x k of
                            LT => adjust $ T h k (delete x (assert_smaller t l)) r
                            EQ => if isEmpty r then l else
                                  if isEmpty l then r else
                                  let (k',l') = delMax l
                                  in adjust $ T h k' l' r
                            GT => adjust $ T h k l (delete x (assert_smaller t r))
  where
    delMax : Tree a -> (a, Tree a)
    delMax t = assert_total $ case t of
                 T h k l E => (k, l)
                 T h k l r => let (k',l') = delMax l in
                                  (k', T h k l' r)
    height : Tree a -> Nat
    height t = case t of
                E         => Z
                T h _ _ _ => h

    isSingle : Tree a -> Bool
    isSingle t = case t of
                   E                    => False
                   T _ _ _ E            => True
                   T h _ _ (T h' _ _ _) => h > h'

    realign : Tree a -> Nat
    realign t = case t of
               T h _ _ _ => if isSingle t then (pred h) else h
               _         => Z

    adjust : Tree a -> Tree a
    adjust E = E
    adjust t@(T h k a b) = assert_total $

      -- Base Case : Both subtrees are below current tree.
      -- Action : No adjustment
      --
      -- h   :   t         t
      --        / \   =>  / \
      -- h-1 : a   b     a   b
      --
      if (height a == pred h) && (height b >= pred h)
        then t

      -- Case 1 : Right subtree is lower than left subtree, and the left
      --          subtree is not a double node.
      -- Action : Lower the height of the current tree and skew to correct.
      --
      -- h   :      t
      --           / \
      -- h-1 :    a   *   =>    a - t
      --         / \   \       /   / \
      -- h-2 :  al  ar  b     al  ar  b
      --
      else if (height b < pred h) && (isSingle a)
        then skew $ T (pred h) k a b

      -- Case 2 : Right subtree is lower than left subtree, and the left
      --          subtree is a double node.
      -- Action : Remove the right node from lefts subtree's double node,
      --          setting this node as the new current tree and reattach
      --          both of its subtrees as inner nodes of the left subtree
      --          and the old current tree.
      --
      -- h   :     _ t _               a2
      --          /     \            /    \
      -- h-1 :   a - a2  *    =>    a      t
      --        /   / \   \        / \    / \
      -- h-2 : al a2l a2r  b      al a2l a2r b
      --
      else if (height b < pred h)
        then let (T ha ka  al  a2)  = a
                 (T ha ka2 a2l a2r) = a2
             in
               T h ka2 (T ha ka al a2l) (T ha k a2r b)


      -- Case 3 : First subtree is deeper than second subtree, and the current
      --          tree is not a double node.
      -- Action : Lower the height of the current tree, and split to correct in
      --          case that subtree b is not single.
      --
      -- h           t                        _b_
      --            / \                     /     \
      -- h-1 :     *   b - b2      =>      t      b2
      --          /   /   /  \            / \    /  \
      -- h-2 :   a   bl  b2l b2r         a  bl  b2l b2r
      --
      else if (height b < h)
        then split $ T (pred h) k a b

      -- Case 4 : First subtree is deeper than second subtree, and the current
      --          tree is a double node.
      -- Action :
      --
      -- h   :     t - b                    __bl_
      --          /   / \                  /     \
      -- h-1 :   *   bl  br        =>     t       b - br
      --        /   / \                  / \     /
      -- h-2 : a  bll blr               a  bll  blr
      --
      -- h   :     t - ___b___              bl -  b
      --          /   /       \            /    /   \
      -- h-1 :   *   bl - blr  br  =>     t    blr  br
      --        /   /     / \            / \
      -- h-2 : a   bll                  a  bll
      --
      else
        let (T h   kb  bl  br)  = b
            (T hbl kbl bll blr) = bl
        in
          T h kbl (T hbl k a bll) (split $ T (realign bl) kb blr br)



||| Convert a tree into a list
export
toList : Tree a -> List a
toList = foldr (::) []


||| Convert a list into a tree
export
fromList : Ord a => List a -> Tree a
fromList = foldr insert empty


-- not very efficient...
export
Eq a => Eq (Tree a) where
  (==) t1 t2 with (compare (order t1) (order t2))
    | EQ = foldr (\x,acc => if x then acc else False) True $
                 zipWith (\x,y => if x == y then True else False)
                         (Tree.toList t1)
                         (Tree.toList t2)
    | _  = False

--}



