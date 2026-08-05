
-- Normalization by evaluation for first-order simply typed
-- lambda calculus with booleans, unit, products and sums via
-- round trip through corresponding Agda terms.

-- Inspired by
--
--   Normalization by Evaluation for λ⃗² by Altenkirch and Uustalu
--     http://www.cs.nott.ac.uk/~txa/publ/flops04.pdf
module FO where

open import Function hiding (_$_)

open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (T ; not ; _≟_)
open import Data.Product hiding (map ; uncurry) renaming (_×_ to _*_)
open import Data.Sum hiding (map)
open import Data.List hiding (map ; [_])

open import Relation.Binary.PropositionalEquality hiding ([_])

-- We need families indexed by more than one kind of 'type', which is
-- slightly more complicated than the usual Bound situation.
Fam : Set → Set₁
Fam I = I → Set

infixr 10 _⇉_
_⇉_ : ∀{I} → Fam I → Fam I → Set
F ⇉ G = ∀{s} → F s → G s

module Var {I : Set} where
  data Var (B : Fam I) (V : Fam I) : Fam I where
    top : B ⇉ Var B V
    pop : V ⇉ Var B V

  bimap : ∀{B C V U} → (B ⇉ C) → (V ⇉ U) → (Var B V ⇉ Var C U)
  bimap f g (top b) = top (f b)
  bimap f g (pop v) = pop (g v)

  map : ∀{B V U} → (V ⇉ U) → (Var B V ⇉ Var B U)
  map = bimap (λ x → x)

  extend : ∀{B V Z} → (V ⇉ Z) → (B ⇉ Z) → (Var B V ⇉ Z)
  extend _   new (top i) = new i
  extend cxt _   (pop v) = cxt v

  data Z : Fam I where

  empty : ∀{V} → Z ⇉ V
  empty ()

  data O (s : I) : Fam I where
    one : O s s

  data T (s t : I) : Fam I where
    one : T s t s
    two : T s t t

  konst : ∀(P : Fam I) {s t} → P s → O s t → P t
  konst P x one = x

open Var public using
  (Var ; top ; pop ; extend ; Z ; empty ; O ; one ; konst ; T ; two)

Scope : ∀{I J} → Fam I → (F : Fam I → Fam J) → Fam I → Fam J
Scope B F V t = F (Var B V) t

-- Our set of base types that may be used as function domains. This
-- excludes higher-order functions.
data Base : Set where
  B U : Base
  _×_ : (a b : Base) → Base
  _+_ : (a b : Base) → Base

-- The types by which our terms are actually indexed; includes base types
-- and functions.
data Type : Set where
  base : (b : Base) → Type
  _⇒_  : (b : Base) → (t : Type) → Type
infixr 10 _⇒_

-- Terms indexed by types with variables in V. Since our calculus is
-- first-order, variables are indexed by base types.
data Term (V : Fam Base) : Fam Type where
  var        : ∀{s}     → V s → Term V (base s)
  _$_        : ∀{s t}   → Term V (s ⇒ t) → Term V (base s) → Term V t
  lam        : ∀{s t}   → Scope (O s) Term V t → Term V (s ⇒ t)
  if         : ∀{s}     → Term V (base B) → Term V s → Term V s → Term V s
  false true :            Term V (base B)
  left       : ∀{a b}   → Term V (base a) → Term V (base (a + b))
  right      : ∀{a b}   → Term V (base b) → Term V (base (a + b))
  either     : ∀{a b t} → Scope (O a) Term V t → Scope (O b) Term V t
                        → Term V (base (a + b)) → Term V t
  _,_        : ∀{a b}   → Term V (base a) → Term V (base b) → Term V (base (a × b))
  uncurry    : ∀{a b t} → Term V (a ⇒ b ⇒ t) → Term V (base (a × b)) → Term V t
  unit       :            Term V (base U)

-- A type of closed terms, without variables
Closed : Fam Type
Closed = Term Z

-- Our base types and function types can be interpreted into Agda types.
[_] : Fam Base
[   B   ] = Bool
[   U   ] = ⊤
[ a × b ] = [ a ] * [ b ]
[ a + b ] = [ a ] ⊎ [ b ]

⟦_⟧ : Fam Type
⟦ base b ⟧ = [ b ]
⟦ s ⇒ t  ⟧ = [ s ] → ⟦ t ⟧

-- Evaluation of our terms into corresponding Agda values is straight forward.
--
-- Note: this time evaluation of our syntax into our semantics trivially passes
-- the termination checker, because it is just a walk over the syntax tree,
-- composing up the relevant Agda value.
--
-- This is a helper function for the real eval. We can only interpret a
-- Term V s into an ⟦ s ⟧ if we know how to interpret all the relevant Vs,
-- And that means we can only really interpret closed terms (or, Term ⟦_⟧)
-- into Agda values.
eval' : ∀{V} → (V ⇉ [_]) → Term V ⇉ ⟦_⟧
eval' cxt (var v)        = cxt v
eval' cxt (f $ x)        = (eval' cxt f) (eval' cxt x)
eval' cxt (lam e)        = λ x → eval' (extend cxt (konst [_] x)) e
eval' cxt (if b t f)     = if eval' cxt b
                             then eval' cxt t
                             else eval' cxt f
eval' _   unit           = _
eval' _   false          = false
eval' _   true           = true
eval' cxt (x , y)        = (eval' cxt x , eval' cxt y)
eval' cxt (left  x)      = inj₁ (eval' cxt x)
eval' cxt (right y)      = inj₂ (eval' cxt y)
eval' cxt (either l r s) with eval' cxt s
... | inj₁ x = eval' (extend cxt (konst [_] x)) l
... | inj₂ y = eval' (extend cxt (konst [_] y)) r
eval' cxt (uncurry e p)  = eval' cxt e (proj₁ ep) (proj₂ ep)
 where
 ep = eval' cxt p

-- Evaluates a closed term to an Agda value.
eval : Closed ⇉ ⟦_⟧
eval = eval' (λ{s} → empty {Base} {[_]})

-- Reflection of values of base type back into terms is also straight-forward.
reflect-base : ∀{V} → (b : Base) → [ b ] → Term V (base b)
reflect-base U _              = unit
reflect-base B false          = false
reflect-base B true           = true
reflect-base (a × b) (x , y)  = reflect-base a x , reflect-base b y
reflect-base (a + b) (inj₁ x) = left  (reflect-base a x)
reflect-base (a + b) (inj₂ y) = right (reflect-base b y)

-- Termination argument:
--   The bad sequence is reflect (a × b ⇒ t) which calls
--   reflect-scope (a × b) t which calls reflect (a ⇒ b ⇒ t).
--   Agda thinks the last is larger than the original, but it
--   is actually the same size, while more amenable to our
--   purposes. I don't anticipate Agda being able to figure
--   this out, though. Termination depth increases don't help.
{-# NO_TERMINATION_CHECK #-}
reflect-scope : ∀{V} → (b : Base) → (t : Type)
              → (f : [ b ] → ⟦ t ⟧) → Scope (O b) Term V t
reflect : ∀{V} → ⟦_⟧ ⇉ Term V

-- Reflect scope turns an Agda function into a fully eta-expanded term
reflect-scope U       t f = reflect (f _)
reflect-scope B       t f = if (var (top one))
                              (reflect (f true))
                              (reflect (f false))
reflect-scope (a × b) t f = uncurry (reflect (curry f)) (var (top one))
reflect-scope (a + b) t f = either
                              (reflect-scope a t (f ∘ inj₁))
                              (reflect-scope b t (f ∘ inj₂))
                              (var (top one))

reflect {V} {base b} x = reflect-base b x
reflect {V} {b ⇒ t}  f = lam (reflect-scope b t f)

-- Normalization is just the composition of evaluation with reflection.
nf : Closed ⇉ Closed
nf = reflect ∘ eval

bump : ∀{V U v u} → (∀ s t → V s → U t → Bool)
                  → (∀(s t : Base) → Var (O v) V s → Var (O u) U t → Bool)
bump p s t (top _)  (top _)  = true
bump p s t (pop v1) (pop v2) = p s t v1 v2
bump _ _ _ _        _        = false

-- Alpha equality of terms
eq : ∀{V U s t} → (∀ s t → V s → U t → Bool) → Term V s → Term U t → Bool
eq vp (var x) (var y) = vp _ _ x y
eq vp (f1 $ x1) (f2 $ x2) = eq vp f1 f2 ∧ eq vp x1 x2
eq vp (lam e1) (lam e2) = eq (bump vp) e1 e2
eq vp (if b1 t1 f1) (if b2 t2 f2) = eq vp b1 b2 ∧ eq vp t1 t2 ∧ eq vp f1 f2
eq vp false false = true
eq vp true true = true
eq vp (left x1) (left x2) = eq vp x1 x2
eq vp (right y1) (right y2) = eq vp y1 y2
eq vp (either l1 r1 e1) (either l2 r2 e2) =
  eq vp e1 e2 ∧ eq (bump vp) l1 l2 ∧ eq (bump vp) r1 r2
eq vp (x1 , y1) (x2 , y2) = eq vp x1 x2 ∧ eq vp y1 y2
eq vp (uncurry f1 p1) (uncurry f2 p2) = eq vp p1 p2 ∧ eq vp f1 f2
eq vp unit unit = true
eq vp _    _    = false

-- Beta-eta equality of closed terms via our normalizer
_≟_ : ∀{s} → Closed s → Closed s → Bool
x ≟ y = eq (λ _ _ ()) (nf x) (nf y)

-- Examples

idb : ∀{V} → Term V (B ⇒ base B)
idb = lam (var (top one))
-- nf idb ==> lam (if (var (top one)) true false)

not : ∀{V} → Term V (B ⇒ base B)
not = lam (if (var (top one)) false true)
-- nf not = lam (if (var (top one)) false true)

notnot : ∀{V} → Term V (B ⇒ base B)
notnot = lam (not $ (not $ (var (top one))))
-- nf notnot ==> lam (if (var (top one)) true false)
-- not ≟ notnot ==> false

notnotnot : ∀{V} → Term V (B ⇒ base B)
notnotnot = lam (not $ (not $ (not $ (var (top one)))))
-- nf notnotnot ==> lam (if (var (top one)) false true)
-- not ≟ notnotnot ==> true

idpu : ∀{V} → Term V (U × U ⇒ base (U × U))
idpu = lam (var (top one))
-- nf idpu ==> lam (uncurry (lam (lam (unit , unit))) (var (top one)))

btos : ∀{V} → Term V (B ⇒ base (U + U))
btos = lam (if (var (top one)) (left unit) (right unit))

stob : ∀{V} → Term V (U + U ⇒ base B)
stob = lam (either true false (var (top one)))

btostob : ∀{V} → Term V (B ⇒ base B)
btostob = lam (stob $ (btos $ (var (top one))))
-- nf btostob ==> lam (if (var (top one)) true false)
-- btostob ≟ idb ==> true

stobtos : ∀{V} → Term V (U + U ⇒ base (U + U))
stobtos = lam (btos $ (stob $ (var (top one))))
-- nf stobtos ==> lam (either (left unit) (right unit) (var (top one)))
