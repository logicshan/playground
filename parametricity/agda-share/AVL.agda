
-- Formalization of how to color an AVL tree as a red black tree,
-- using the argument here:
--   https://cs.stackexchange.com/q/134326/93254

module AVL where

open import Function
open import Data.Nat
open import Data.Product

data Tree : Set where
  leaf : Tree
  node : Tree → Tree → Tree

data Color : Set where
  red black : Color

variable
  t l r : Tree
  c d : Color
  m n : ℕ

-- Red-black colorings of a binary tree
--
-- The color index is the root color.
-- The natural number index is the black height.
-- Leaves are not counted as increasing the black height, just
-- for simplicity matching up with the AVL height.
data Coloring : Tree → Color → ℕ → Set where
  leaf : Coloring leaf black 0
  red
    : Coloring l black m
    → Coloring r black m
    → Coloring (node l r) red m
  black
    : Coloring l c m
    → Coloring r d m
    → Coloring (node l r) black (suc m)

-- Proof that a tree satisfies the AVL condition.
--
-- The natural number index is the height of the tree.
data AVL : Tree → ℕ → Set where
  leaf : AVL leaf 0
  minus : AVL l (1 + m) → AVL r m → AVL (node l r) (2 + m)
  plus  : AVL l m → AVL r (1 + m) → AVL (node l r) (2 + m)
  equal : AVL l m → AVL r m → AVL (node l r) (1 + m)

-- Uses the height of a tree to choose a root color and a
-- black height for coloring the tree.
colorization : ℕ → Color × ℕ
colorization 0 = black , 0
colorization (suc n) with colorization n
... | red   , m = black , 1 + m
... | black , m = red   , m

parity : ℕ → Color
parity = proj₁ ∘ colorization

black-height₀ : ℕ → ℕ
black-height₀ = proj₂ ∘ colorization

-- A valid red black tree must have the root colored black,
-- so this calculates the final black height after fixing
-- the color chosen by the previous function.
black-height : ℕ → ℕ
black-height n with colorization n
... | black , m = m
... | red   , m = 1 + m

-- Turn a red-rooted tree black-rooted
char : Coloring t red n → Coloring t black (suc n)
char (red l r) = black l r

-- Calculate a coloring of an AVL tree allowing for a red
-- root.
color₀ : AVL t n → Coloring t (parity n) (black-height₀ n)
color₀ leaf = leaf
color₀ (minus {m = m} l r) with colorization m | color₀ l | color₀ r
... | red   , _ | cl | cr = red cl (char cr)
... | black , _ | cl | cr = black cl cr
color₀ (plus {m = m} l r) with colorization m | color₀ l | color₀ r
... | red   , _ | cl | cr = red (char cl) cr
... | black , _ | cl | cr = black cl cr
color₀ (equal {m = m} l r) with colorization m | color₀ l | color₀ r
... | red   , _ | cl | cr = black cl cr
... | black , _ | cl | cr = red cl cr

-- Calculate a coloring of an AVL tree ensuring that the root is
-- black.
color : AVL t n → Coloring t black (black-height n)
color {n = n} a with colorization n | color₀ a
... | red   , _ | ct = char ct
... | black , _ | ct = ct
