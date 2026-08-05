{-# OPTIONS --guardedness #-}

module Sub where

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Literals
open import Agda.Builtin.FromNat
open import Data.Product

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality hiding (subst)

-- A simple system of types for a language of computational terms
--
-- booleans, naturals, unit, closed terms and functions.
--
-- The type system includes a type for the language's own closed
-- terms to avoid having to think about encoding them as natural
-- numbers or similar.
data Ty : Set where
  bo na un da : Ty
  tm li : Ty → Ty
  _⇒_ : Ty → Ty → Ty
infixr 10 _⇒_

-- A context for open terms is just a left-nested list of types.
-- This is for keeping track of the types of variables in a term.
data Ctx : Set where
  [] : Ctx
  _∷_ : Ctx → Ty → Ctx
infixl 10 _∷_

variable
  A B C : Set
  r s t u v : Ty
  Γ Δ Θ : Ctx

-- A type of syntax trees for (open) terms, indexed by a context
-- giving types for the variables, as well as the type of term.
--
-- Most of the terms are fairly standard. The usual types have
-- constructors and eliminators. The oddities are as follows:
--
-- - Variables are written in de Bruijn style, but where one can
--   'pop' an entire tree, to indicate that the entire subterm
--   doesn't make use of the variable.
--
-- - The eliminator for naturals is just one-step case analysis,
--   because ...
--
-- - There is a term for forming arbitrary fixed points. Its type is
--   reminiscent of `fix` in a lazy language, just (r → r) → r. But
--   the evaluator below is actually eager, so effectively the code
--   is added to the environment, and must be manually evaluated.
--   This makes it easier to write the required quine-like program,
--   too, since you automatically have the code of recursion.
--
-- - Any closed term can be quoted
--
-- - Quoted terms can be turned into a raw representation as rose
--   trees. Tags in the node correspond to constructors of this data
--   type, and there is a list of similarly encoded subterms.
data Tm : Ctx → Ty → Set where
  -- variables: top, pop
  to : Tm (Γ ∷ t) t
  po : Tm Γ t → Tm (Γ ∷ u) t

  -- unit
  tt : Tm Γ un

  -- bool: false, true, if
  fa tr : Tm Γ bo
  if : Tm Γ bo → Tm Γ r → Tm Γ r → Tm Γ r

  -- nat: 0, suc, case
  ze : Tm Γ na
  su : Tm Γ na → Tm Γ na
  ca : Tm Γ na → Tm Γ r → Tm (Γ ∷ na) r → Tm Γ r

  -- lists: nil, cons, case
  ni : Tm Γ (li t)
  co : Tm Γ t → Tm Γ (li t) → Tm Γ (li t)
  uc : Tm Γ (li t) → Tm Γ r → Tm (Γ ∷ t ∷ li t) r → Tm Γ r

  -- function: λ apply
  la : Tm (Γ ∷ u) v → Tm Γ (u ⇒ v)
  ap : Tm Γ (u ⇒ v) → Tm Γ u → Tm Γ v

  -- recursion: lazy recurse, force
  re : Tm (Γ ∷ tm r) r → Tm Γ r
  fo : Tm Γ (tm r) → Tm Γ r

  -- reflection: quoting, to raw data rep, data case
  gö : Tm [] v → Tm Γ (tm v)
  ra : Tm Γ (tm t) → Tm Γ da
  cn : Tm Γ na → Tm Γ (li da) → Tm Γ da
  dc : Tm Γ da → Tm (Γ ∷ na ∷ li da) r → Tm Γ r

instance
  term-number : Number (Tm Γ na)
  term-number .Number.Constraint _ = ⊤
  term-number .Number.fromNat zero = ze
  term-number .Number.fromNat (suc n) = su (term-number .Number.fromNat n)

-- Converts a term into its rose tree representation.
--
-- Paramterized by a root-level constructor for a type, so that
-- it can be used to produce both terms and values.
toData : ∀{R : Set} → (Tm Δ na → Tm Δ (li da) → R) → Tm Γ t → R
toData con = λ where
    to → con 0 ni
    (po e) → con 1 (co (rec e) ni)
    tt → con 2 ni
    fa → con 3 ni
    tr → con 4 ni
    (if e t f) → con 5 (co (rec e) (co (rec t) (co (rec f) ni)))
    ze → con 6 ni
    (su e) → con 7 (co (rec e) ni)
    (ca e z s) → con 8 (co (rec e) (co (rec z) (co (rec s) ni)))
    ni → con 9 ni
    (co x xs) → con 10 (co (rec x) (co (rec xs) ni))
    (uc l n c) → con 11 (co (rec l) (co (rec n) (co (rec c) ni)))
    (la e) → con 12 (co (rec e) ni)
    (ap f x) → con 13 (co (rec f) (co (rec x) ni))
    (re e) → con 14 (co (rec e) ni)
    (fo e) → con 15 (co (rec e) ni)
    (gö e) → con 16 (co (rec e) ni)
    (ra e) → con 17 (co (rec e) ni)
    (cn n e) → con 18 (co (rec n) (co (rec e) ni))
    (dc d e) → con 19 (co (rec d) (co (rec e) ni))
  where
  rec : Tm Γ t → Tm Δ da
  rec = toData cn

-- Values for the substituting evaluator. Terms are only
-- evaluated until some sort of constructor is reached.
data Va : Ty → Set where
  tt : Va un
  fa tr : Va bo
  ze : Va na
  ni : Va (li t)
  co : Tm [] t → Tm [] (li t) → Va (li t)
  su : (n : Tm [] na) → Va na
  la : Tm ([] ∷ s) t → Va (s ⇒ t)
  gö : Tm [] t → Va (tm t)
  cn : Tm [] na → Tm [] (li da) → Va da

-- The value version of the above rose tree representation.
toVal : Tm Γ t → Va da
toVal = toData cn

-- A convenient type for tracking substitution of one term into
-- another. The evaluator only does this one or two at a time so
-- a simplified type can be used.
--
-- A `Sub Γ Δ` contains information for substituting into a
-- `Term Γ t` to obtain a `Term Δ t`.
data Sub : Ctx → Ctx → Set where
  on : Tm [] t → Sub ([] ∷ t) []
  tw : Tm [] t → Tm [] u → Sub ([] ∷ t ∷ u) []
  pu : Sub Γ Δ → Sub (Γ ∷ t) (Δ ∷ t)

-- Given a substitution, produces a term in a new context.
subst : Sub Γ Δ → Tm Γ r → Tm Δ r
-- structure
subst _   tt = tt
subst _   fa = fa
subst _   tr = tr
subst sub (if e t f) = if (subst sub e) (subst sub t) (subst sub f)
subst _   ze = ze
subst sub (su n) = su (subst sub n)
subst sub (ca e z s) = ca (subst sub e) (subst sub z) (subst (pu sub) s)
subst _   ni = ni
subst sub (co x xs) = co (subst sub x ) (subst sub xs)
subst sub (uc l n c) = uc (subst sub l) (subst sub n) (subst (pu (pu sub)) c) 
subst sub (la e) = la (subst (pu sub) e)
subst sub (ap f e) = ap (subst sub f) (subst sub e)
subst sub (re e) = re (subst (pu sub) e)
subst sub (fo e) = fo (subst sub e)
subst _   (gö e) = gö e
subst sub (ra e) = ra (subst sub e)
subst sub (cn n b) = cn (subst sub n) (subst sub b)
subst sub (dc d c) = dc (subst sub d) (subst (pu (pu sub)) c)

-- variables
subst (on e) to = e
subst (tw _ e) to = e
subst (pu _) to = to
subst (on _) (po e) = e
subst (tw o _) (po e) = subst (on o) e
subst (pu sub) (po e) = po (subst sub e)

-- Step and Eval are machinery for describing partial recursive
-- functions/computations. The simple now/later construction is
-- not well suited to this substitution evaluator. It's difficult
-- to make the guardedness checker accept the code. Making
-- sequencing guarded via »= is much easier.
data Step (A : Set) : Set
record Eval (A : Set) : Set

data Step A where
  now : A → Step A
  _»=_ : Eval (Va t) → (Va t → Eval A) → Step A
  later : Eval A → Step A

record Eval A where
  coinductive
  field
    force : Step A
open Eval

-- The substituting evaluator. The entire process here manipulates
-- only closed terms. Only substitution above ever has to go
-- underneath binders.
--
-- This essentially implements call-by-name evaluation. Unevaluated
-- terms are substituted into all occurrences of a variable.
eval : Tm [] r → Eval (Va r)
step : Tm [] r → Step (Va r)

eval e .force = step e

step tt = now tt
step fa = now fa
step tr = now tr
step ze = now ze
step (if e t f) = eval e »= λ where
  fa → eval f
  tr → eval t
step (su e) = now (su e)
step (ca e z s) = eval e »= λ where
  ze → eval z
  (su e) → eval (subst (on e) s)
step ni = now ni
step (co x xs) = now (co x xs)
step (uc l n c) = eval l »= λ where
  ni → eval n
  (co x xs) → eval (subst (tw x xs) c)
step (la e) = now (la e)
step (ap f x) = eval f »= λ where (la e) → eval (subst (on x) e)
step (re e) = later (eval (subst (on (gö (re e))) e))
step (fo e) = eval e »= λ where (gö x) → eval x
step (gö e) = now (gö e)
step (ra e) = eval e »= λ where
  (gö e) .force → now (toVal e)
step (cn n e) = now (cn n e)
step (dc d c) = eval d »= λ where
  (cn t b) → eval (subst (tw t b) c)

quot : Va r → Tm [] r
quot tt = tt
quot fa = fa
quot tr = tr
quot ze = ze
quot ni = ni
quot (co x xs) = co x xs
quot (su n) = su n
quot (la e) = la e
quot (gö x) = gö x
quot (cn t as) = cn t as

-- ↓ represents a convergence proof of a partial computation.
--
-- px ↓ x means that the partial computation px converges to x
_↓_ : Eval A → A → Set
data Con : Step A → A → Set

px ↓ x = Con (force px) x

data Con where
  now : ∀{x : A} → Con (now x) x
  later : ∀{px} {x : A} → px ↓ x → Con (later px) x
  _»=_ : ∀{px f} {x : Va t} {y : B} → px ↓ x → f x ↓ y → Con (px »= f) y

eval-quot : ∀(va : Va t) → eval (quot va) ↓ va
eval-quot tt = now
eval-quot fa = now
eval-quot tr = now
eval-quot ze = now
eval-quot ni = now
eval-quot (co x xs) = now
eval-quot (su n) = now
eval-quot (la x) = now
eval-quot (gö x) = now
eval-quot (cn x as) = now

-- ↑ represents a divergence proof of a partial computation.
record _↑ (px : Eval A) : Set
data Div : Step A → Set

record _↑ px where
  coinductive
  field
    force : Div (force px)
open _↑

data Div where
  pre : ∀{px : Eval (Va t)} {f : Va t → Eval B} → px ↑ → Div (px »= f)
  post : ∀{px} {x : Va t} {f : Va t → Eval B} → px ↓ x → f x ↑ → Div (px »= f)
  later : ∀{px : Eval A} → px ↑ → Div (later px)

-- A partial computation cna only converge to one value.
coherent : ∀{sx} {x y : A} → Con sx x → Con sx y → x ≡ y
coherent now now = refl
coherent (later sy) (later sz) = coherent sy sz
coherent (x »= f) (y »= g) rewrite coherent x y = coherent f g

-- A partial computation cannot both converge and diverge.
dichotomous : ∀{px} {x : A} → px ↑ → px ↓ x → ⊥
dichotomous div con = st (force div) con where
  st : ∀{sx} {x} → Div sx → Con sx x → ⊥
  st (later d) (later c) = dichotomous d c
  st (pre d) (c »= _) = dichotomous d c
  st (post x r) (y »= f) rewrite coherent x y = dichotomous r f

-- A term halts if there is a value its evaluation converges to.
Halts : Tm [] t → Set
Halts e = Σ[ v ∈ Va _ ] eval e ↓ v

-- A term diverges if its evaluation diverges.
Diverges : Tm [] t → Set
Diverges e = eval e ↑

ReflectsHalting : Tm [] un → Va bo → Set _
ReflectsHalting e fa = Diverges e
ReflectsHalting e tr = Halts e

-- A halting decider is a function from code to booleans that
-- always converges. It must converge to true if its argument
-- halts, and false if its argument diverges.
isHaltingDecider : Tm [] (tm un ⇒ bo) → Set _
isHaltingDecider ha =
  ∀ e → Σ[ h ∈ Halts (ap ha (gö e)) ] ReflectsHalting e (proj₁ h)

-- ha is a proposed halting decider, mapping closed terms to
-- booleans. It is supposed to return true if its argument
-- converges, and false if its argument diverges.
module Halt (ha : Tm [] (tm un ⇒ bo)) where
  -- The diagonal term.
  --
  -- di = if halts di then di else ()
  di : Tm [] un
  di = re (if (ap (po ha) to) (fo to) tt)

  -- if ha di = true, then di diverges, so ha is wrong
  module D (ans : eval (ap ha (gö di)) ↓ tr) where
    diverge : eval di ↑
    diverge .force = later λ where
      .force → post ans λ where .force → post now diverge

  -- if ha di = false, then di converges, so ha is wrong
  module H (ans : eval (ap ha (gö di)) ↓ fa) where
    halts : eval di ↓ tt
    halts = later (ans »= now)

  -- ha is not a halting decider
  halting-problem : ¬ isHaltingDecider ha
  halting-problem is-dec with is-dec di
  ... | (fa , ans) , div = dichotomous div (H.halts ans)
  ... | (tr , ans) , con = dichotomous (D.diverge ans) (con .proj₂)

module Rice
  -- Suppose there is a type A realized by a Ty RA
  {A : Set} {RA : Ty}
  -- ⊨ explains how (object) values realize semantic values
  (_⊨_ : Va RA → A → Set)
  -- Suppose there's a semantic value x ...
  (x : A)
  -- ... that is realized by an (object) value ry ...
  (ry : Va RA) (ry⊨x :   ry ⊨ x)
  -- ... and not realized by every (object) value.
  (rn : Va RA) (rn⊭x : ¬ rn ⊨ x)
  -- ri is a candidate for deciding whether a program computes a realizer
  (ri : Tm [] (tm RA ⇒ bo))
  where
  ReflectsRealization : Tm [] RA → Va bo → Set
  ReflectsRealization t tr = ∀ va → eval t ↓ va →   va ⊨ x
  ReflectsRealization t fa = ∀ va → eval t ↓ va → ¬ va ⊨ x

  isRealizerDecider : Set
  isRealizerDecider =
    ∀ tm → Σ[ h ∈ Halts (ap ri (gö tm)) ] ReflectsRealization tm (proj₁ h)

  -- The diagonal program. Tests ri's result on itself then does the opposite.
  di : Tm [] RA
  di = re (if (ap (po ri) to) (po (quot rn)) (po (quot ry)))

  di-lemma : Halts (ap ri (gö di)) → Halts di
  di-lemma (fa , hfa) .proj₁ = ry
  di-lemma (fa , hfa) .proj₂ = later (hfa »= eval-quot ry)
  di-lemma (tr , htr) .proj₁ = rn
  di-lemma (tr , htr) .proj₂ = later (htr »= eval-quot rn)

  -- If ri answers yes on di, then di evaluates to a non-realizer.
  module N (ans : eval (ap ri (gö di)) ↓ tr) where
    di↓rn : eval di ↓ rn
    di↓rn = later (ans »= eval-quot rn)

  -- If ri answers no on di, then di evaluates to a realizer.
  module Y (ans : eval (ap ri (gö di)) ↓ fa) where
    di↓ry : eval di ↓ ry
    di↓ry = later (ans »= eval-quot ry)

  -- ri cannot possibly decide whether programs compute realizers.
  rice's-theorem : ¬ isRealizerDecider
  rice's-theorem is-dec with is-dec di
  ... | (fa , ans), nope = nope ry (Y.di↓ry ans) ry⊨x
  ... | (tr , ans), yep  = rn⊭x (yep rn (N.di↓rn ans))
