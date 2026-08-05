
-- Normalization by evaluation for the SK combinator calculus.
-- To keep things very simple, we don't bother with types, meaning
-- the calculus is not strongly normalizing, and we must disable
-- the termination checker.

-- The strategy here is to use normal forms of the SK calclulus as
-- the semantic domain, which is somewhat boring, but gets the job
-- done.
module SK where

-- The syntax of the combinator calculus has S, K and application
data Syntax : Set where
  S K : Syntax
  _$_ : (f x : Syntax) → Syntax
infixl 90 _$_

-- The semantics of the calculus include S applied to 0, 1 or 2 semantic
-- values, and K applied to 0 or 1 semantic value. Further applications
-- are redexes, and thus are not in normal form.
data Semantics : Set where
  S₀ K₀ : Semantics
  S₁ K₁ : (  x : Semantics) → Semantics
  S₂    : (f g : Semantics) → Semantics

-- Application can be defined on normal forms, with recursion once S
-- becomes fully applied.
{-# NO_TERMINATION_CHECK #-}
_$$_ : (f x : Semantics) → Semantics
S₀     $$ y = S₁ y
K₀     $$ y = K₁ y
S₁ f   $$ y = S₂ f y
K₁ x   $$ y = x
S₂ f g $$ y = (f $$ y) $$ (g $$ y)

-- Evaluation of syntax to semantics follows in the obvious way.
eval : Syntax → Semantics
eval S       = S₀
eval K       = K₀
eval (f $ x) = eval f $$ eval x

-- Reflection of semantic values back into syntax is also easy.
reflect : Semantics → Syntax
reflect S₀       = S
reflect K₀       = K
reflect (S₁ f)   = S $ reflect f
reflect (K₁ x)   = K $ reflect x
reflect (S₂ f g) = S $ reflect f $ reflect g
