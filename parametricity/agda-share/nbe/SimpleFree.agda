
-- Normalization by evaluation for the simply typed lambda calculus
-- with empty, unit, sum and product types.
module SimpleFree where

open import Function using (_∘_)

import Bound

data Type : Set where
  ∅ ∙ : Type
  _×_ _+_ _⇒_ : (s t : Type) → Type
infixr 10 _⇒_
infixr 20 _+_
infixr 30 _×_

open Bound Type

-- Fam = Type -> Set

-- Terms with variables in V, indexed by the type of the term.
data Term (V : Fam) : Fam where
  var    :        V ⇉ Term V
  _$_    : ∀{s t}   → Term V (s ⇒ t) → Term V s → Term V t
  lam    : ∀{s t}   → Scope (O s) Term V t → Term V (s ⇒ t)
  _,_    : ∀{s t}   → Term V s → Term V t → Term V (s × t)
  fst    : ∀{s t}   → Term V (s × t ⇒ s)
  snd    : ∀{s t}   → Term V (s × t ⇒ t)
  left   : ∀{s t}   → Term V (s ⇒ s + t)
  right  : ∀{s t}   → Term V (t ⇒ s + t)
  either : ∀{s t r} → Term V ((s ⇒ r) ⇒ (t ⇒ r) ⇒ s + t ⇒ r)
  void   : ∀{s}     → Term V (∅ ⇒ s)
  unit   :            Term V ∙
infixl 90 _$_
infixl 60 _,_

-- Our semantic domain is to contain only representations of the normal forms
-- of the above type, but we must split it into two parts to get there.
data Neutral (V : Fam) : Fam
data Normal (V : Fam) : Fam

-- Neutral terms are 'stuck', and are not eligible for reduction.
-- They are variables and all the fully saturated terms whose
-- computation is blocked by other neutral terms.
data Neutral V where
  var     : V ⇉ Neutral V
  _$_     : ∀{s t} → Neutral V (s ⇒ t) → Normal V s → Neutral V t
  either₃ : ∀{s t r} → Normal  V (s ⇒ r)
                     → Normal  V (t ⇒ r)
                     → Neutral V (s + t)
                     → Neutral V r
  fst₁    : ∀{s t} → Neutral V (s × t) → Neutral V s
  snd₁    : ∀{s t} → Neutral V (s × t) → Neutral V t
  void₁   : ∀{s}   → Neutral V ∅ → Neutral V s

-- Normal terms are those that are in fully reduced form, including
-- neutral terms, under-saturated terms and those that don't compute.
data Normal V where
  neutral : Neutral V ⇉ Normal V
  lam     : ∀{s t}   → Scope (O s) Normal V t → Normal V (s ⇒ t)
  _,_     : ∀{s t}   → Normal V s → Normal V t → Normal V (s × t)
  left₀   : ∀{s t}   → Normal V (s ⇒ s + t)
  left₁   : ∀{s t}   → Normal V s → Normal V (s + t)
  right₀  : ∀{s t}   → Normal V (t ⇒ s + t)
  right₁  : ∀{s t}   → Normal V t → Normal V (s + t)
  either₀ : ∀{s t r} → Normal V ((s ⇒ r) ⇒ (t ⇒ r) ⇒ s + t ⇒ r)
  either₁ : ∀{s t r} → Normal V (s ⇒ r) → Normal V ((t ⇒ r) ⇒ s + t ⇒ r)
  either₂ : ∀{s t r} → Normal V (s ⇒ r) → Normal V (t ⇒ r) → Normal V (s + t ⇒ r)
  fst₀    : ∀{s t}   → Normal V (s × t ⇒ s)
  snd₀    : ∀{s t}   → Normal V (s × t ⇒ t)
  void₀   : ∀{s}     → Normal V (∅ ⇒ s)
  unit    :            Normal V ∙

-- Given indexed mappings from V to U, we can map both normal and neutral terms
map-o : ∀{V U} → (V ⇉ U) → Normal V ⇉ Normal U
map-e : ∀{V U} → (V ⇉ U) → Neutral V ⇉ Neutral U

map-o f (neutral n)   = neutral (map-e f n)
map-o f (lam e)       = lam (map-o (Var.map f) e)
map-o f (x , y)       = map-o f x , map-o f y
map-o f left₀         = left₀
map-o f (left₁ x)     = left₁ (map-o f x)
map-o f right₀        = right₀
map-o f (right₁ x)    = right₁ (map-o f x)
map-o f either₀       = either₀
map-o f (either₁ l)   = either₁ (map-o f l)
map-o f (either₂ l r) = either₂ (map-o f l) (map-o f r)
map-o f fst₀          = fst₀
map-o f snd₀          = snd₀
map-o f void₀         = void₀
map-o f unit          = unit

map-e f (var v)         = var (f v)
map-e f (g $ x)         = map-e f g $ map-o f x
map-e f (either₃ l r s) = either₃ (map-o f l) (map-o f r) (map-e f s)
map-e f (fst₁ p)        = fst₁ (map-e f p)
map-e f (snd₁ p)        = snd₁ (map-e f p)
map-e f (void₁ x)       = void₁ (map-e f x)

-- Normal is an indexed monad
pure : ∀{V} → V ⇉ Normal V
pure = neutral ∘ var

-- _*_ is the substitution operation for the Normal monad.
-- _^_ is a similar operation on neutral terms, yielding normal terms
-- _$$_ is application of normal terms, yielding a normal term
--
-- The types we have indexed our normal, neutral and syntactic terms by should
-- ensure termination, because the simply typed lambda calculus is strongly
-- normalizing. But such an argument is non-trivial, so no effort is made to
-- satisfy the termination checker.

{-# NO_TERMINATION_CHECK #-}
_*_ : ∀{V U} → (V ⇉ Normal U) → Normal V ⇉ Normal U
_^_ : ∀{V U} → (V ⇉ Normal U) → Neutral V ⇉ Normal U
_$$_ : ∀{V s t} → Normal V (s ⇒ t) → Normal V s → Normal V t

f * neutral n = f ^ n
f * lam e       = lam (extend (map-o pop ∘ f) (pure ∘ top) * e)
f * (x , y)     = (f * x) , (f * y)
f * left₀       = left₀
f * left₁  x    = left₁ (f * x)
f * right₀      = right₀
f * right₁ x    = right₁ (f * x)
f * either₀     = either₀
f * either₁ l   = either₁ (f * l)
f * either₂ l r = either₂ (f * l) (f * r)
f * fst₀        = fst₀
f * snd₀        = snd₀
f * void₀       = void₀
f * unit        = unit

f ^ var x         = f x
f ^ (g $ x)       = (f ^ g) $$ (f * x)
f ^ either₃ l r s = either₂ (f * l) (f * r) $$ (f ^ s)
f ^ fst₁  p       = fst₀ $$ (f ^ p)
f ^ snd₁  p       = snd₀ $$ (f ^ p)
f ^ void₁ s       = void₀ $$ (f ^ s)

instantiate : ∀{B V} → (B ⇉ Normal V) → Normal (Var B V) ⇉ Normal V
instantiate f e = extend pure f * e

neutral f   $$ x         = neutral (f $ x)
lam e       $$ x         = instantiate (konst (Normal _) x) e
left₀       $$ x         = left₁ x
right₀      $$ x         = right₁ x
either₀     $$ l         = either₁ l
either₁ l   $$ r         = either₂ l r
either₂ l r $$ neutral x = neutral (either₃ l r x)
either₂ l r $$ left₁   x = l $$ x
either₂ l r $$ right₁  y = r $$ y
fst₀        $$ neutral p = neutral (fst₁ p)
fst₀        $$ (x , y)   = x
snd₀        $$ neutral p = neutral (snd₁ p)
snd₀        $$ (x , y)   = y
void₀       $$ neutral x = neutral (void₁ x)

-- With the above machinery, evaluation of syntactic terms to semantic
-- normal forms is again easy.
eval : ∀{V} → Term V ⇉ Normal V
eval (var v) = neutral (var v)
eval (f $ x) = eval f $$ eval x
eval (lam e) = lam (eval e)
eval (x , y) = eval x , eval y
eval fst     = fst₀
eval snd     = snd₀
eval left    = left₀
eval right   = right₀
eval either  = either₀
eval void    = void₀
eval unit    = unit

-- Reflection of normal and neutral terms back into syntax is also straight forward.
reflect' : ∀{V} → Neutral V ⇉ Term V
reflect : ∀{V} → Normal V ⇉ Term V

reflect' (var v)         = var v
reflect' (f $ x)         = reflect' f $ reflect x
reflect' (either₃ l r s) = either $ reflect l $ reflect r $ reflect' s
reflect' (fst₁ p)        = fst $ reflect' p
reflect' (snd₁ p)        = snd $ reflect' p
reflect' (void₁ v)       = void $ reflect' v

reflect (neutral n)   = reflect' n
reflect (lam e)       = lam (reflect e)
reflect (x , y)       = reflect x , reflect y
reflect left₀         = left
reflect (left₁ x)     = left $ reflect x
reflect right₀        = right
reflect (right₁ x)    = right $ reflect x
reflect either₀       = either
reflect (either₁ l)   = either $ reflect l
reflect (either₂ l r) = either $ reflect l $ reflect r
reflect fst₀          = fst
reflect snd₀          = snd
reflect void₀         = void
reflect unit          = unit

-- Composition yields a normalization procedure.
nf : ∀{V} → Term V ⇉ Term V
nf = reflect ∘ eval

-- Exmaples

id : ∀{V t} → Term V (t ⇒ t)
id = lam (var (top one))

cmp : ∀{V s t u} → Term V ((t ⇒ u) ⇒ (s ⇒ t) ⇒ (s ⇒ u))
cmp = lam (lam (lam
        (var (pop (pop (top one))) $
          (var (pop (top one)) $ var (top one)))))
-- nf (cmp $ id $ id) ==> lam (var (top one))
