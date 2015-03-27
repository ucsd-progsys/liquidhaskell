Case Study: AVL Trees {#case-study-avltree}
================================


\begin{comment}
\begin{code}
{- Example of AVL trees by michaelbeaumont -}

{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--totality"       @-}

module AVL (AVL, empty, singleton, insert, insert', delete) where

import qualified Data.Set as S
import Prelude hiding (max)
-- import Language.Haskell.Liquid.Prelude (liquidAssume)

-- Test
main = do
    mapM_ print [a, b, c, d]
  where
    a = singleton 5
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c

-- | Height is actual height (will disappear with measure-generated-invariants) ------------

{-@ invariant {v:AVL a | 0 <= realHeight v && realHeight v = getHeight v} @-}

{-@ inv_proof  :: t:AVL a -> {v:_ | 0 <= realHeight t && realHeight t = getHeight t } @-}
inv_proof Leaf           = True
inv_proof (Node k l r n) = inv_proof l && inv_proof r

{-@ node :: x:a -> l:AVLL a x -> r:{AVLR a x | isBal l r 1} -> {v:AVL a | realHeight v = nodeHeight l r} @-}
node v l r = Node v l r (nodeHeight l r)

balR0, balRL, balRR :: a -> AVL a -> AVL a -> AVL a
insR :: a -> AVL a -> AVL a
merge :: a -> AVL a -> AVL a -> AVL a
member :: (Ord a) => a -> AVL a -> Bool
-- FIXME bigHt l r t  = if (realHeight l >= realHeight r) then (eqOrUp l t) else (eqOrUp r t)
\end{code}
\end{comment}


One of the most fundamental abstractions in computing is that of a
*collection* of values -- names, numbers, records -- into which we can
rapidly `insert`, `delete` and check for `member`ship.

\newthought{Trees} offer an an attractive means of implementing
collections in the immutable setting. We can *order* the values
to ensure that each operation takes time proportional to the
*path* from the root to the datum being operated upon.
If we additionally keep the tree *balanced* then each path
is small (relative to the size of the collection), thereby
giving us an efficient implementation for collections.

\newthought{As in real life}
maintaining order and balance is rather easier said than done.
Often we must go through rather sophisticated gymnastics to ensure
everything is in its right place. Fortunately, LiquidHaskell can help.
Lets see a concrete example, that should be familiar from your introductory
data structures class: the Georgy Adelson-Velsky and Landis' or [AVL Tree][avl-wiki].

AVL Trees
---------

An `AVL` tree is defined by the following Haskell datatype:^[This chapter is based on code by Michael Beaumont.]

\begin{code}
data AVL a =
    Leaf
  | Node { key :: a      -- value
         , l   :: AVL a  -- left subtree
         , r   :: AVL a  -- right subtree
         , ah  :: Int    -- height
         }
    deriving (Show)
\end{code}

While the Haskell type signature describes any old binary tree, an
`AVL` tree like that shown in Figure [auto](#fig:avl) actually satisfies
two crucial invariants: it should be binary search ordered and
balanced.

<div class="marginfigure"
     id="fig:avl"
     height="150px"
     file="img/avl.png"
     caption="An AVL tree is an ordered, height-balanced tree.">
</div>

\newthought{A Binary Search Ordered} tree is one where at *each*
`Node`, the values of the `left` and `right` subtrees are strictly
less and greater than the values at the `Node`. In the
tree in Figure [auto](#fig:avl) the root has value `50` while its left
and right subtrees have values in the range `9-23` and `54-76`
respectively.  This holds at all nodes, not just the root. For
example, the node `12` has left and right children strictly less and
greater than `12`.

\newthought{A Balanced} tree is one where at *each* node, the *heights*
of the left and right subtrees differ by at most `1`. In
Figure [auto](#fig:avl), at the root, the heights of the left and right subtrees
are the same, but at the node `72` the left subtree has height `2` which is
one more then the right subtree.

\newthought{The Invariants Lead To Fast Operations.}
Order ensures that there is at most a single path of `left` and
`right` moves from the root at which an element can be found; balance
ensures that each such path in the tree is of size $O(\log\ n)$ where
$n$ is the numbers of nodes. Thus, together they ensure that the
collection operations are efficient: they take time logarithmic in the
size of the collection.

Specifying AVL Trees
--------------------

The tricky bit is to ensure order and balance. Before we can ensure
anything, lets tell LiquidHaskell what we mean by these terms, by
defining legal or valid AVL trees.

\newthought{To Specify Order} we just define two aliases `AVLL` and `AVLR`
-- read *AVL-left* and *AVL-right* -- for trees whose values are strictly less
than and greater than some value `X`:

\begin{code}
-- | Trees with value less than X
{-@ type AVLL a X = AVL {v:a | v < X}  @-}

-- | Trees with value greater than X
{-@ type AVLR a X = AVL {v:a | X < v}  @-}
\end{code}


\newthought{The Real Height} of a tree is defined recursively as `0`
for `Leaf`s and one more than the larger of left and right subtrees
for `Node`s.  Note that we cannot simply use the `ah` field because
thats just some arbitrary `Int` -- there is nothing to prevent a buggy
implementation from just filling that field with `0` everywhere.  In
short, we need the ground truth: a measure that computes the *actual*
height of a tree. ^[**FIXME** The `inline` pragma indicates that the
Haskell functions can be directly lifted into and used inside the
refinement logic and measures.]

\begin{code}
{-@ measure realHeight @-}
realHeight                :: AVL a -> Int
realHeight Leaf           = 0
realHeight (Node _ l r _) = nodeHeight l r

{-@ inline nodeHeight @-}
nodeHeight l r = 1 + max hl hr
  where
    hl         = realHeight l
    hr         = realHeight r

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y
\end{code}

\newthought{A Reality Check} predicate ensures that a value
`v` is indeed the *real* height of a node with subtrees `l` and `r`:

\begin{code}
{-@ inline isReal @-}
isReal v l r = v == nodeHeight l r
\end{code}

\newthought{A Node is $n$-Balanced} if its left and right subtrees
have a (real) height difference of at most $n$. We can specify this
requirement as a predicate `isBal l r n`

\begin{code}
{-@ inline isBal @-}
isBal l r n = 0 - n <= d && d <= n
  where
    d       = realHeight l - realHeight r
\end{code}

\newthought{A Legal AVL Tree} can now be defined via the following
[refined data type](#refineddatatypes), which states that each `Node`
is $1$-balanced, and that the saved height field is indeed the *real* height:

\begin{code}
{-@ data AVL a = Leaf
               | Node { key :: a
                      , l   :: AVLL a key
                      , r   :: {v:AVLR a key | isBal l v 1}
                      , ah  :: {v:Nat        | isReal v l r}
                      }                                  @-}
\end{code}

Smart Constructors
------------------

Lets use the type to construct a few small trees which will
also be handy in a general collection API. First, lets write
an alias for trees of a given height:

\begin{code}
-- | Trees of height N
{-@ type AVLN a N = {v: AVL a | realHeight v = N} @-}

-- | Trees of height equal to that of another T
{-@ type AVLT a T = AVLN a {realHeight T} @-}
\end{code}

\newthought{An Empty} collection is represented by a `Leaf`,
which has height `0`:

\begin{code}
{-@ empty :: AVLN a 0 @-}
empty = Leaf
\end{code}

<div class="hwex" id="Singleton">
Consider the function `singleton` that builds an `AVL`
tree from a single element. Fix the code below so that
it is accepted by LiquidHaskell.
</div>

\begin{code}
{-@ singleton :: a -> AVLN a 1 @-}
singleton x =  Node x empty empty 0
\end{code}

As you can imagine, it can be quite tedious to keep the saved height
field `ah` *in sync* with the *real* height. In general in such
situations, which arose also with [lazy queues](#lazyqueue), the right
move is to eschew the data constructor and instead use a *smart
constructor* that will fill in the appropriate values correctly. ^[Why
bother to save the height anyway? Why not just recompute it instead?]

\newthought{The Smart Constructor} `node` takes as input the node's value `x`,
left and right subtrees `l` and `r` and returns a tree by filling in the right
value for the height field.

\begin{code}
{-@ mkNode :: a -> l:AVL a -> r:AVL a
           -> AVLN a {nodeHeight l r}
  @-}
mkNode v l r = Node v l r h
 where
   h       = 1 + max hl hr
   hl      = getHeight l
   hr      = getHeight r
\end{code}

<div class="hwex" id="Constructor">Unfortunately, LiquidHaskell  rejects
the above smart constructor `node`. Can you explain why? Can you fix the
code (implementation or specification) so that the function is accepted?
</div>

\hint Think about the (refined) type of the actual constructor `Node`, and
the properties it requires and ensures.


Inserting Elements
------------------

Next, lets turn our attention to the problem of *adding* elements to
an `AVL` tree. The basic strategy is this:

1. *Find* the appropriate location (per ordering) to add the value,
2. *Replace* the `Leaf` at that location with the singleton value.

\noindent If you prefer the spare precision of code to the
informality of English, here is a first stab at implementing
insertion: ^[`node` is a fixed variant of the smart
constructor `mkNode`. Do the exercise *without* looking at it.]


\begin{code}
{-@ insert0    :: (Ord a) => a -> AVL a -> AVL a @-}
insert0 y t@(Node x l r _)
  | y < x      = insL0 y t
  | x < y      = insR0 y t
  | otherwise  = t
insert0 y Leaf = singleton y

insL0 y (Node x l r _) = node x (insert0 y l) r
insR0 y (Node x l r _) = node x l (insert0 y r)
\end{code}


\newthought{Unfortunately} `insert0` does not work.
If you did the exercise above, you can replace it with `mkNode` and
you will see that the above function is rejected by LiquidHaskell.
The error message would essentially say that at the calls to the
smart constructor, the arguments violate the balance requirement.

\newthought{Insertion Increases The Height} of a sub-tree, making
it *too large* relative to its sibling. For example, consider the
tree `t0` defined as:

~~~~~{.ghci}
ghci> let t0 = Node { key = 'a'
                    , l   = Leaf
                    , r   = Node {key = 'd'
                                 , l  = Leaf
                                 , r  = Leaf
                                 , ah = 1 }
                    , ah = 2}
~~~~~

If we use `insert0` to add the key `'e'` (which goes after `'d'`) then we end up
with the result:

\vfill

~~~~~{.ghci}
ghci> insert0 'e' t0
  Node { key = 'a'
       , l   = Leaf
       , r   = Node { key = 'd'
                    , l   = Leaf
                    , r   = Node { key = 'e'
                                 , l   = Leaf
                                 , r   = Leaf
                                 , ah  = 1   }
                    , ah = 2                 }
       , ah = 3}
~~~~~

<div class="marginfigure"
     height="150px"
     file="img/avl-insert0.png"
     id="fig:avl-insert0"
     caption="Naive insertion breaks balancedness">
</div>


\noindent In the above, illustrated in Figure [auto](#fig:avl-insert0)
the value `'e'` is inserted into the valid tree `t0`; it is inserted
using `insR0`, into the *right* subtree of `t0` which already has
height `1` and causes its height to go up to `2` which is too large
relative to the empty left subtree of height `0`.

\newthought{LiquidHaskell catches the imbalance} by rejecting `insert0`.
The new value `y` is inserted into the right subtree `r`, which (may
already be bigger than the left by a factor of `1`).
As insert can return a tree with arbitrary height, possibly
much larger than `l` and hence, LiquidHaskell rejects the call to
the constructor `node` as the balance requirement does not hold.

\newthought{Two lessons} can be drawn from the above exercise. First,
`insert` may *increase* the height of a tree by at most `1`. So,
second, we need a way to *rebalance* sibling trees where one has
height `2` more than the other.

Rebalancing Trees
-----------------

The brilliant insight of Adelson-Velsky and Landis was that we can,
in fact, perform such a rebalancing with a clever bit of gardening.
Suppose we have inserted a value into the *left* subtree `l` to
obtain a new tree `l'` (the right case is symmetric.)

\newthought{The relative heights} of `l'` and `r` fall under one of three cases:

+ *(RightBig)* `r`  is two more than `l'`,
+ *(LeftBig)*  `l'` is two more than `r`, and otherwise
+ *(NoBig)*    `l'` and `r` are within a factor of `1`,

\newthought{We can specify} these cases as follows.

\begin{code}
{-@ inline leftBig @-}
leftBig l r = diff l r == 2

{-@ inline rightBig @-}
rightBig l r = diff r l == 2

{-@ inline diff @-}
diff s t = getHeight s - getHeight t
\end{code}

\noindent the function `getHeight` accesses the saved height field.

\begin{code}
{-@ measure getHeight @-}
getHeight Leaf           = 0
getHeight (Node _ _ _ n) = n
\end{code}

In `insL`, the *RightBig* case cannot arise as `l'` is at least as
big as `l`, which was within a factor of `1` of `r` in the valid
input tree `t`.  In *NoBig*, we can safely link  `l'` and `r` with
the smart constructor as they satisfy the balance requirements.
The *LeftBig* case is the tricky one: we need a way to shuffle
elements from the left subtree over to the right side.

\newthought{What is a LeftBig tree?} Lets split into the possible
cases for `l'`, immediately ruling out the *empty* tree because
its height is `0` which cannot be `2` larger than any other tree.

+ *(NoHeavy)* the left and right subtrees of `l'` have the same height,
+ *(LeftHeavy)* the left subtree of `l'` is bigger than the right,
+ *(RightHeavy)* the right subtree of `l'` is bigger than the left.

\newthought{The Balance Factor} of a tree can be used to make the above
cases precise. Note that while the `getHeight` function returns the saved
height (for efficiency), thanks to the invariants, we know it is in fact
equal to the `realHeight` of the given tree.

\begin{code}
{-@ measure balFac @-}
balFac Leaf           = 0
balFac (Node _ l r _) = getHeight l - getHeight r
\end{code}

\newthought{Heaviness} can be encoded by testing the balance factor:

\begin{code}
{-@ inline leftHeavy @-}
leftHeavy  t = balFac t > 0

{-@ inline rightHeavy @-}
rightHeavy t = balFac t < 0

{-@ inline noHeavy @-}
noHeavy    t = balFac t == 0
\end{code}

Adelson-Velsky and Landis observed that once you've drilled
down  into these three cases, the shuffling suggests itself.

<div class="figure"
     id="fig:avl-balL0"
     height="150px"
     file="img/avl-balL0.png"
     caption="Rotating when in the LeftBig, NoHeavy case.">
</div>

\newthought{In the NoHeavy} case, illustrated in
Figure [auto](#fig:avl-balL0),
the subtrees  `ll` and `lr` have the same height which is one more than that
of `r`. Hence, we can link up `lr` and `r` and link the result with `l`.
Here's how you would implement the rotation. Note how the preconditions
capture the exact case we're in: the left subtree is *NoHeavy* and the right
subtree is smaller than the left by `2`. Finally, the output type captures
the exact height of the result, relative to the input subtrees.

\begin{code}
{-@ balL0 :: x:a
          -> l:{AVLL a x | noHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLN a {realHeight l + 1 }
  @-}
balL0 v (Node lv ll lr _) r = node lv ll (node v lr r)
\end{code}

<div class="figure"
     height="150px"
     file="img/avl-balLL.png"
     caption="Rotating when in the LeftBig, LeftHeavy case."
     id="fig:avl-balLL">
</div>

\newthought{In the LeftHeavy} case, illustrated in
Figure [auto](#fig:avl-balLL), the subtree `ll` is larger than `lr`;
hence `lr` has the same height as `r`, and again we can link up
`lr` and `r` and link the result with `l`. As in the *NoHeavy* case,
the input types capture the exact case, and the output the height of
the resulting tree.

 \begin{code}
{-@ balLL :: x:a
          -> l:{AVLL a x | leftHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLT a l
  @-}
balLL v (Node lv ll lr _) r = node lv ll (node v lr r)
\end{code}

<div class="figure"
     height="150px"
     file="img/avl-balLR.png"
     caption="Rotating when in the LeftBig, RightHeavy case."
     id="fig:avl-balLR">
</div>

\newthought{In the RightHeavy} case, illustrated in Figure [auto](#fig:avl-balLR),
the subtree  `lr` is larger than  `ll`. We cannot directly link it with `r` as
the result would again be too large. Hence, we split it further into its own
subtrees `lrl` and `lrr` and link the latter with `r`. Again, the types capture
the requirements and guarantees of the rotation.

\begin{code}
{-@ balLR :: x:a
          -> l:{AVLL a x | rightHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLT a l
  @-}
balLR v (Node lv ll (Node lrv lrl lrr _) _) r
  = node lrv (node lv ll lrl) (node v lrr r)
\end{code}


The *RightBig* cases are symmetric to the above cases where the
left subtree is the larger one.

<div class="hwex" id="RightBig, NoHeavy">
Fix the implementation of `balR0` so that it implements the given type.
</div>

\vspace{1.0in}
\vspace*{\fill}

\begin{code}
{-@ balR0 :: x:a
          -> l: AVLL a x
          -> r: {AVLR a x | rightBig l r && noHeavy r}
          -> AVLN a {realHeight r + 1}
  @-}
balR0 v l r = undefined
\end{code}

<div class="hwex" id="RightBig, RightHeavy">
Fix the implementation of `balRR` so that it implements the given type.
</div>


\begin{code}
{-@ balRR :: x:a
          -> l: AVLL a x
          -> r:{AVLR a x | rightBig l r && rightHeavy r}
          -> AVLT a r
  @-}
balRR v l r = undefined
\end{code}

<div class="hwex" id="RightBig, LeftHeavy">
Fix the implementation of `balRL` so that it implements the given type.
</div>

\begin{code}
{-@ balRL :: x:a
          -> l: AVLL a x
          -> r:{AVLR a x | rightBig l r && leftHeavy r}
          -> AVLT a r
  @-}
balRL v l r = undefined
\end{code}


\newthought{To Correctly Insert} an element, we recursively add it
to the left or right subtree as appropriate and then determine which
of the above cases hold in order to call the corresponding *rebalance*
function which restores the invariants.

\begin{code}
{-@ insert :: a -> s:AVL a -> {t: AVL a | eqOrUp s t} @-}
insert y Leaf = singleton y
insert y t@(Node x _ _ _)
  | y < x     = insL y t
  | y > x     = insR y t
  | otherwise = t
\end{code}

\noindent The refinement, `eqOrUp` says that the height of `t` is the same
as `s` or goes *up* by atmost `1`.

\begin{code}
{-@ inline eqOrUp @-}
eqOrUp s t = d == 0 || d == 1
  where
    d      = diff t s
\end{code}

\newthought{The hard work} happens inside `insL` and `insR`. Here's the
first; it simply inserts into the left subtree to get `l'` and then determines
which rotation to apply.

\begin{code}
{-@ insL :: x:a
         -> t:{AVL a | x < key t && 0 < realHeight t}
         -> {v: AVL a | eqOrUp t v}
  @-}
insL a (Node v l r _)
  | isLeftBig && leftHeavy l'  = balLL v l' r
  | isLeftBig && rightHeavy l' = balLR v l' r
  | isLeftBig                  = balL0 v l' r
  | otherwise                  = node  v l' r
  where
    isLeftBig                  = leftBig l' r
    l'                         = insert a l
\end{code}

<div class="hwex" id="InsertRight"> \singlestar
\noindent The code for `insR` is symmetric. To make sure you're
following along, why don't you fill it in?
</div>

\begin{code}
{-@ insR :: x:a
         -> t:{AVL a  | key t < x && 0 < realHeight t }
         -> {v: AVL a | eqOrUp t v}
  @-}
insR = undefined
\end{code}

Refactoring Rebalance
---------------------

Next, lets write a function to `delete` an element from a tree.
In general, we can apply the same strategy as `insert`:

1. remove the element without worrying about heights,
2. observe that deleting can *decrease* the height by at most `1`,
3. perform a rotation to fix the imbalance caused by the decrease.

\newthought{We painted ourselves into a corner} with `insert`: the code
for actually inserting an element is intermingled with the code for
determining and performing the rotation. That is, see how the code
that determines which rotation to apply -- `leftBig`, `leftHeavy`, etc. --
is *inside* the `insL` which does the insertion as well.
This is correct, but it means we would have to *repeat* the case
analysis when deleting a value, which is unfortunate.

\newthought{Instead lets refactor} the rebalancing code into a
separate function, that can be used by *both* `insert` and `delete`.
It looks like this:

\begin{code}
{-@ bal :: x:a
        -> l:AVLL a x
        -> r:{AVLR a x | isBal l r 2}
        -> {t:AVL a | reBal l r t}
  @-}
bal v l r
  | isLeftBig  && leftHeavy l  = balLL v l r
  | isLeftBig  && rightHeavy l = balLR v l r
  | isLeftBig                  = balL0 v l r
  | isRightBig && leftHeavy r  = balRL v l r
  | isRightBig && rightHeavy r = balRR v l r
  | isRightBig                 = balR0 v l r
  | otherwise                  = node  v l r
  where
    isLeftBig                  = leftBig l r
    isRightBig                 = rightBig l r
\end{code}

The `bal` function is a combination of the case-splits and rotation calls
made by `insL` (and ahem, `insR`); it takes as input a value `x` and valid
left and right subtrees for `x` whose heights are off by at most `2` because
as we will have created them by inserting or deleting a value from a sibling
whose height was at most `1` away. The `bal` function returns a valid `AVL` tree,
whose height is constrained to satisfy the predicate `reBal l r t`, which says:

+ (`bigHt`) The height of `t` is the same or one bigger than the larger of `l` and `r`, and
+ (`balHt`) If `l` and `r` were already balanced (i.e. within `1`) then the height
   of `t` is exactly equal to that of a tree built by directly linking `l`
   and `r`.

\begin{code}
{-@ inline reBal @-}
reBal l r t = bigHt l r t && balHt l r t

{-@ inline balHt @-}
balHt l r t = not (isBal l r 1) || isReal (realHeight t) l r

{-@ inline bigHt @-}
bigHt l r t = lBig && rBig
  where
    lBig    = not (hl >= hr) || (eqOrUp l t)
    rBig    = (hl >= hr)     || (eqOrUp r t)
    hl      = realHeight l
    hr      = realHeight r
\end{code}

\newthought{Insert} can now be written very simply as the following function that
recursively inserts into the appropriate subtree and then calls `bal` to fix any imbalance:

\begin{code}
{-@ insert' :: a -> s:AVL a -> {t: AVL a | eqOrUp s t} @-}
insert' a t@(Node v l r n)
  | a < v      = bal v (insert' a l) r
  | a > v      = bal v l (insert' a r)
  | otherwise  = t
insert' a Leaf = singleton a
\end{code}

Deleting Elements
-----------------

Now we can write the `delete` function in a manner similar to `insert`:
the easy cases are the recursive ones; here we just delete from the
subtree and summon `bal` to clean up. Notice that the height of the
output `t` is at most `1` *less* than that of the input `s`.

\begin{code}
{-@ delete    :: a -> s:AVL a -> {t:AVL a | eqOrDn s t} @-}
delete y (Node x l r _)
  | y < x     = bal x (delete y l) r
  | x < y     = bal x l (delete y r)
  | otherwise = merge x l r
delete _ Leaf = Leaf

{-@ inline eqOrDn @-}
eqOrDn s t = eqOrUp t s
\end{code}

\newthought{The tricky case} is when we actually *find* the
element that is to be removed. Here, we call `merge` to link
up the two subtrees `l` and `r` after hoisting the smallest
element from the right tree `r` as the new root which replaces
the deleted element `x`.

\begin{code}
{-@ merge :: x:a -> l:AVLL a x -> r:{AVLR a x | isBal l r 1}
          -> {t:AVL a | bigHt l r t}
  @-}
merge _ Leaf r = r
merge _ l Leaf = l
merge x l r    = bal y l r'
  where
   (y, r')     = getMin r
\end{code}

`getMin` recursively finds the smallest (i.e. leftmost) value
in a tree, and returns the value and the remainder tree.  The height
of each remainder `l'` may be lower than `l` (by at most `1`.) Hence,
we use `bal` to restore the invariants when linking against the
corresponding right subtree `r`.

\begin{code}
getMin (Node x Leaf r _) = (x, r)
getMin (Node x l r _)    = (x', bal x l' r)
  where
    (x', l')             = getMin l
\end{code}


Functional Correctness
----------------------

We just saw how to implement some tricky data structure gynastics.
Fortunately, with LiquidHaskell as a safety net we can be sure to have
gotten all the rotation cases right and to have preserved the
invariants crucial for efficiency and correctness.  However, there is
nothing in the types above that captures "functional correctness",
which, in this case, means that the operations actually implement a
collection or set API, for example, as described [here](#mapapi).
Lets use the techniques from that chapter to precisely specify
and verify that our AVL operations indeed implement sets correctly, by:

1. *Defining* the set of elements in a tree,
2. *Specifying* the desired semantics of operations via types,
3. *Verifying* the implemetation. ^[By adding [ghost operations](#lemmas), if needed.]

We've done this [once before](#lemmas) already, so this is a good exercise
to solidify your understanding of that material.

\newthought{The Elements} of an `AVL` tree can be described via a measure
defined as follows:

\begin{code}
{-@ measure elems @-}
elems                :: (Ord a) => AVL a -> S.Set a
elems (Node x l r _) = (S.singleton x) `S.union`
                       (elems l)       `S.union`
                       (elems r)
elems Leaf           = S.empty
\end{code}

\noindent Let us use the above `measure` to specify and verify that our `AVL` library
actually implements a `Set` or collection API.


<div class="hwex" id="Membership">Complete the implementation of the implementation of
`member` that checks if an element is in an `AVL` tree:
</div>

\begin{code}
-- FIXME https://github.com/ucsd-progsys/liquidhaskell/issues/332
{-@ member :: (Ord a) => x:a -> t:AVL a -> {v: Bool | Prop v <=> hasElem x t} @-}
member x t = undefined

{-@ type BoolP P = {v:Bool | Prop v <=> Prop P} @-}

{-@ inline hasElem @-}
hasElem x t = True
-- FIXME hasElem x t = S.member x (elems t)
\end{code}


<div class="hwex" id="Insertion">Modify `insert'` to obtain
a function `insertAPI` that states that the output tree
contains the newly inserted element (in addition to the old elements):
</div>

\begin{code}
{-@ insertAPI :: (Ord a) => a -> s:AVL a -> {t:AVL a | addElem x s t} @-}
insertAPI x s = insert' x s

{-@ inline addElem @-}
addElem       :: Ord a => a -> AVL a -> AVL a -> Bool
addElem x s t = True
-- FIXME addElem x s t = (elems t) == (elems s) `S.union` (S.singleton x)
\end{code}


<div class="hwex" id="Insertion">Modify `delete` to obtain
a function `deleteAPI` that states that the output tree
contains the old elements minus the removed element:
</div>

\begin{code}
{-@ deleteAPI :: (Ord a) => a -> s:AVL a -> {t: AVL a | delElem x s t} @-}
deleteAPI x s = delete x s

{-@ inline delElem @-}
delElem       :: Ord a => a -> AVL a -> AVL a -> Bool
delElem x s t = True
-- FIXME delElem x s t = (elems t) == (elems s) `S.difference` (S.singleton x)
\end{code}
