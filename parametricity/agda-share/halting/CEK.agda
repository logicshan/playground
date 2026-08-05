{-# OPTIONS --guardedness #-}

module CEK where

open import Level using (Level) renaming (suc to ℓ-suc)

open import Data.Bool
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Unit

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

variable
  ℓ : Level
  A B : Set ℓ

-- Part implements potentially diverging computations in a simple way.
-- A value of type Part A is a potentially infinite number of delay
-- steps, with finite sequences having an A value at the end.
--
-- "Part" stands for "partial," as in partial recursive function.
record Part (A : Set ℓ) : Set ℓ
data Step (A : Set ℓ) : Set ℓ

record Part A where
  coinductive
  field
    force : Step A
open Part

data Step A where
  now : A → Step A
  later : Part A → Step A

-- ↡ represents convergence proofs of a partial computation.
_↡_ : (px : Part A) (x : A) → Set _
data _↓_ {A : Set ℓ} : Step A → A → Set ℓ

px ↡ x = force px ↓ x

data _↓_  where
  now : ∀ x → now x ↓ x
  later : ∀{p x} → p ↡ x → later p ↓ x

-- ↟ represents divergence proofs of a partial computation.
record _↟ {A : Set ℓ} (px : Part A) : Set ℓ
data _↑ {A : Set ℓ} : Step A → Set ℓ

record _↟ px where
  coinductive
  field
    force : force px ↑
open _↟

data _↑ where
  later : ∀{px} → px ↟ → later px ↑

-- A partial computation cannot both converge and diverge.
dichotomy : ∀{pa : Part A} {a} → pa ↡ a → pa ↟ → ⊥
dichotomy {pa = pa} {a} div con = descend div (force con) where
  descend : ∀{pa} → pa ↓ a → pa ↑ → ⊥
  descend (later d) (later c) = descend d (force c)

-- A simple system of types for a language of computational terms
--
-- booleans, naturals, unit, closed terms and functions.
--
-- The type system includes a type for the language's own closed
-- terms to avoid having to think about encoding them as natural
-- numbers or similar.
data Ty : Set where
  bo na un : Ty
  tm : Ty → Ty
  _⇒_ : Ty → Ty → Ty
infixr 10 _⇒_

-- A context for open terms is just a left-nested list of types.
-- This is for keeping track of the types of variables in a term.
data Ctx : Set where
  [] : Ctx
  _∷_ : Ctx → Ty → Ctx
infixl 10 _∷_

variable
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
-- - There is a term of type `tm v ⇒ bo` that represents a proposed
--   halting predicate. The terms do not depend on the particular
--   predicate, in the syntax, it's just an arbitrary function symbol.
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

  -- function: λ apply
  la : Tm (Γ ∷ u) v → Tm Γ (u ⇒ v)
  ap : Tm Γ (u ⇒ v) → Tm Γ u → Tm Γ v

  -- recursion: lazy recurse, force
  re : Tm (Γ ∷ tm r) r → Tm Γ r
  fo : Tm Γ (tm r) → Tm Γ r

  -- reflection: quoting and halting
  gö : Tm [] v → Tm Γ (tm v)
  ha : Tm Γ (tm v ⇒ bo)

-- The diagonal term
--
--   di = if halts di then di else ()
di : Tm Γ un
di = re (if (ap ha to) (fo to) tt)

-- A type for reifying evaluation results to types that look nicer.
-- Functions are just ignored, because it's tricky to build a way of
-- extracting them.
Rei : Ty → Set
Rei bo = Bool
Rei na = ℕ
Rei un = ⊤
Rei (tm t) = Tm [] t
Rei (t ⇒ u) = ⊤

-- Evaluator types
--
-- Env is a collection of values for a context.
--
-- Cl is a suspended closure; an Env Γ together with a Tm Γ t
--
-- Ko is a type of continuations specifying what to do when the
-- primary term is fully evaluated.
--
-- Va is a fully evaluated term.
data Env : Ctx → Set
record Cl (t : Ty) : Set
data Ko : Ty → Ty → Set
data Va : Ty → Set

data Ko where
  -- empty
  [] : Ko r r
  -- boolean case
  if : (env : Env Γ) (t f : Tm Γ s) → (k : Ko s r) → Ko bo r
  -- nat case
  ca : (env : Env Γ) (z : Tm Γ t) (s : Tm (Γ ∷ na) t) → (k : Ko t r) → Ko na r
  -- successor
  su : Ko na r → Ko na r
  -- suspend argument
  ar : (v : Cl t) → (k : Ko u r) → Ko (t ⇒ u) r
  -- push argument value
  pu : (v : Va t) → (k : Ko u r) → Ko (t ⇒ u) r
  -- eval body
  ev : (env : Env Γ) (e : Tm (Γ ∷ s) t) → Ko t r → Ko s r
  -- force
  fo : Ko t r → Ko (tm t) r
  -- halting
  ha : Ko bo r → Ko (tm t) r

data Env where
  [] : Env []
  _∷_ : Env Γ → Va t → Env (Γ ∷ t)

record Cl t where
  inductive
  constructor pack
  field
    {ctx} : Ctx
    env : Env ctx
    code : Tm ctx t

data Va where
  tt : Va un
  fa tr : Va bo
  ze : Va na
  su : Va na → Va na
  la : Env Γ → Tm (Γ ∷ s) t → Va (s ⇒ t)
  gö : Env Γ → Tm Γ t → Va (tm t)
  ha : Va (tm t ⇒ bo)

-- A Sub is a type for substituting an environment back into an
-- open term to get a closed term.
--
-- Sub Γ Δ can take a `Tm Γ t` to a `Tm Δ t`, but it is simplified
-- to ultimately result in a `Tm [] t`.
data Sub : Ctx → Ctx → Set where
  [] : Sub [] []
  _∷_ : Sub Γ [] → Tm [] t → Sub (Γ ∷ t) []
  pu : Sub Γ Δ → Sub (Γ ∷ t) (Δ ∷ t)

-- quot takes a value to the reduced term representing the value
--
-- env→sub gets the substitution from an environment for producing
-- a closed term
--
-- subst is the main procedure for substituting into an open term.
quot : Va r → Tm [] r
env→sub : Env Γ → Sub Γ []
subst : Sub Γ Δ → Tm Γ r → Tm Δ r

quot tt = tt
quot fa = fa
quot tr = tr
quot ze = ze
quot ha = ha
quot (su n) = su (quot n)
quot (la env e) = la (subst (pu (env→sub env)) e)
quot (gö env e) = gö (subst (env→sub env) e)

bool : Bool → Va bo
bool false = fa
bool  true = tr

env→sub [] = []
env→sub (vs ∷ v) = env→sub vs ∷ quot v

subst _   tt = tt
subst _   fa = fa
subst _   tr = tr
subst _   ze = ze
subst _   ha = ha
subst sub (su e) = su (subst sub e)
subst sub (if e t f) = if (subst sub e) (subst sub t) (subst sub f)
subst sub (ca e z s) = ca (subst sub e) (subst sub z) (subst (pu sub) s)
subst sub (la e) = la (subst (pu sub) e)
subst sub (ap f e) = ap (subst sub f) (subst sub e)
subst sub (re e) = re (subst (pu sub) e)
subst sub (fo e) = fo (subst sub e)
subst sub (gö e) = gö e

subst (_ ∷ v) to = v
subst (pu _) to = to
subst (sub ∷ _) (po e) = subst sub e
subst (pu sub) (po e) = po (subst sub e)

-- The evaluator for terms.
--
-- The structure is something like a CEK machine. At each step, there
-- is a focused term, an environment and a continuation. focus walks
-- into the term, pushing things onto the continuation. When something
-- irreducible is encountered, control transfers to return, which walks
-- back up the continuation with the value.
--
-- The evaluator is parameterized by an arbitrary function, which is
-- used to implement the `ha` term. This can be _any_ function from
-- closed terms to booleans implementable in Agda. This ensures
-- automatically that it's total, and doesn't require implementing it
-- in the embedded language with some kind of encoding or hard to use
-- eliminator. This also, of course, establishes that Agda (the
-- metalanguage) is incapable of deciding halting of this language,
-- not just the embedded language itself. An analogous construction
-- could be done with a term implemented entirely in the embedded
-- language, but it would take more effort to follow the reduction.
module Eval
  (h : ∀{t} → Tm [] t → Bool)
  where

  eval : Env Γ → Tm Γ t → Ko t r → Part (Va r)
  focus : Env Γ → Tm Γ t → Ko t r → Step (Va r)
  return : Va t → Ko t r → Step (Va r)

  eval env e k .force = focus env e k

  focus _ tt k = return tt k
  focus _ fa k = return fa k
  focus _ tr k = return tr k
  focus _ ze k = return ze k
  focus _ ha k = return ha k
  focus env (la e) k = return (la env e) k
  focus (_ ∷ v) to k = return v k
  focus _   (gö e) k = return (gö [] e) k

  focus (env ∷ _) (po e) k = focus env e k

  focus env (if b t f) k = later (eval env b (if env t f k))
  focus env (ca e z s) k = later (eval env e (ca env z s k))
  focus env (su e) k = later (eval env e (su k))
  focus env (ap f x) k = later (eval env f (ar (pack env x) k))
  focus env (re e) k = later (eval (env ∷ gö env (re e)) e k)
  focus env (fo e) k = later (eval env e (fo k))

  return v [] = now v
  return fa (if env t f k) = focus env f k
  return tr (if env t f k) = focus env t k
  return ze (ca env z s k) = focus env z k
  return (su n) (ca env z s k) = focus (env ∷ n) s k
  return n (su k) = return (su n) k
  return (la env e) (pu x k) = focus (env ∷ x) e k
  return ha (pu v k) = return (bool (h (quot v))) k
  return (gö env e) (ha k) = return (bool (h (subst (env→sub env) e))) k
  return v (ev env e k) = focus (env ∷ v) e k
  return (gö env e) (fo k) = focus env e k
  return (la env' e) (ar (pack env c) k) = later (eval env c (ev env' e k))
  return ha (ar (pack env e) k) = focus env e (ha k)

  -- Reify a value to a value that prints nicer. Don't bother with functions.
  reify : Va t → Rei t
  reify tt = _
  reify fa = false
  reify tr = true
  reify ze = 0
  reify ha = _
  reify (su n) = suc (reify n)
  reify (la _ _) = _
  reify (gö env e) = subst (env→sub env) e

  -- This is the environment that will be involved in the recursive
  -- evaluation of `di`.
  dienv : Env ([] ∷ tm un)
  dienv = [] ∷ gö [] di

  -- A proof that if `h di = true`, then evaluation of `di` diverges,
  -- so `h` is wrong about `di` halting.
  module Div (yes : h di ≡ true) where
    diag₀ : eval [] di [] ↟
    diag₁ : eval dienv (if (ap ha to) (fo to) tt) [] ↟
    diag₂ : eval dienv (ap ha to) (if dienv (fo to) tt []) ↟
    diag₃ : eval dienv ha (ar (pack dienv to) (if dienv (fo to) tt [])) ↟
    diag₄ : eval dienv to (fo []) ↟

    diag₀ .force = later diag₁
    diag₁ .force = later diag₂
    diag₂ .force = later diag₃
    diag₃ .force rewrite yes = later diag₄
    diag₄ .force = later diag₁

  -- A proof that if `h di = false`, then evaluation of `di` halts,
  -- so `h` is wrong about `di` diverging.
  module Hal (no : h di ≡ false) where
    diag₀ : eval [] di [] ↡ tt
    diag₁ : return (bool (h di)) (if dienv (fo to) tt []) ↓ tt

    diag₀ = later (later (later diag₁))
    diag₁ rewrite no = now tt

  Halts : Tm [] t → Set
  Halts e = Σ[ v ∈ _ ] (eval [] e [] ↡ v)

  Diverges : Tm [] t → Set
  Diverges e = eval [] e [] ↟

  -- The type of proofs that h is a halting decider. If `h e` is true,
  -- then e must halt, and e must diverge otherwise.
  isHaltDecider : Set
  isHaltDecider = ∀{t} (e : Tm [] t) → if h e then Halts e else Diverges e

  -- h is not a halting decider
  halting-problem : ¬ isHaltDecider
  halting-problem p with h di in eq | p di
  ... | false | div = dichotomy (Hal.diag₀ eq) div
  ... |  true | (v , con) = dichotomy con (Div.diag₀ eq)
