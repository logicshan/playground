{-
-- Identity types
------------------------------------------------------------

Con : Set
Sub : Con → Con → Set
Ty  : Con → Set
Tm  : (Γ : Con) → Ty Γ → Set

------------------------------------------------------------

-- A type for equality proofs.
-- internal reasoning with equalities.

-- (Curry-Howard representation of logical statements)
-- Π
-- Σ
-- ⊤
-- ⊥

-- (types can be viewed as logical propositions)

-- types      |   logical formulas
--------------------------------
-- A ⇒ B      |      A ⊃ B
-- A × B      |      A ∧ B
-- Either A B |      A ∨ B
-- Π A B      |   ∀ (x : A). B
-- Σ A B      |   ∃ (x : A). B
-- Id A t u   |      t = u          (where t : A, u : A)


-- 1. Type formation

Id : (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ   -- type former depending on two terms

    p : Tm Γ (Id Nat n m)   -- this means that assuming Γ, I have a proof that "n" and "m" are equal numbers

-- 1. Construction rule

refl   : (t : Tm Γ A) → Tm Γ (Id A t t)           -- everything is equal to itself ("reflexivity")
refl[] : (refl t)[σ] = refl (t[σ])


-- 2. Elimination rule

-- First look at non-dependent eliminator
--              (Leibniz principle, substitution of equals in any context)

-- "transport"  (in any dependent type B, I can swap t for u)
Transp   : (B : Ty (Γ, A)){t u : Tm Γ A}(p : Tm Γ (Id A t u)) → Tm Γ (B[id, t]) → Tm Γ (B[id, u])
Transp[] : (Transp B p Bt)[σ] = Transp (B[σ⁺]) (p[σ]) (Bt[σ])
Transpβ  : Transp B (refl t) Bt = Bt
       --  Transp B (refl t) Bt : Tm Γ (B[id, t])
       --  Bt : Tm Γ (B[id, t])
-}

open import Relation.Binary.PropositionalEquality renaming (_≡_ to Id) hiding (sym; trans; J)
open import Data.Nat
open import Data.Bool

-- universe in Agda
U = Set

Transp : {A : Set}(B : A → U){x y : A} → Id x y → B x → B y  -- assume Transp is primitive operation
Transp B refl Bx = Bx

-- Id is an equivalence relation
-- refl OK
-- symmetry
-- transitivity

sym : {A : Set}{x y : A} → Id x y → Id y x
sym {A}{x}{y} p = Transp (λ y → Id y x) p refl
            -- ? : Id y x
            -- Transp by (p : Id x y) allows rewriting y to x in the goal
            -- Transp (λ y → Id y x) p : Id x x

trans : {A : Set}{x y z : A} → Id x y → Id y z → Id x z
trans {A}{x}{y}{z} p q = Transp (λ z → Id x z) q p
            -- homework: do instead Transp on p
            --           do Transp on both p and q
            -- (alternative solutions)

-- Id is congruence for functions
ap : {A B : Set}(f : A → B){x y : A} → Id x y → Id (f x) (f y)
ap {A} {B} f {x} {y} p = Transp (λ y → Id (f x) (f y)) p refl

-- are Id proof unique?
-- (bit like an η-rule for Id)
UIP : {A : Set}(t : A)(p : Id t t) → Id {A = Id t t} p refl
UIP = {!!}
   -- this is not derivable
   -- important variation between type theories: do we have UIP or not

{-
-- (for types given by isomorphisms, we always have η)
-- Tm Γ (⊤ + ⊤) ≃ (Tm Γ ⊤) + (Tm Γ ⊤)
-- Tm Γ (Σ A B) ≃ (t : Tm Γ A) × (Tm Γ (B[id, t]))

-- Can we specify Id as an isomorphism? (Yes, we get UIP as part of the isomorphism)

-- what about this: Tm Γ (Id A t u) ≃ (t = u)        -- (metatheoretic equality of t and u)

-- one direction: refl : (t = u) → Tm Γ (Id t u)      (same as the old refl)
-- other        : Tm Γ (Id t u) → (t = u)             (this a new thing)


-- Equality reflection:
-- Reflect : Tm Γ (Id t u) → (t = u)

-- refl/Reflect form an isomorphism, we get UIP (only if the metatheory has UIP)

-- If we have refl, Reflect, UIP                       :   "extensional type theory" (ETT)
-- If we only have (refl, dependent version of Transp) :   "intensional type theory" (ITT)

-- Property of ETT: typechecking / equality of terms/types     are all undecidable
-- Why is ETT undecidable?

-- Inuition: ETT does not have enough annotations
---          Reflect rule allows us to omit transports

-- example: let's prove symmetry using equality reflection

sym : {A : Set}{x y : A}(p : Id x y) → Id y x
sym {A}{x}{y} p = p            -- as soon as I have (p : Id x y) in scope, x and y are freely interchangeable
                               -- without having to use Transport!
                               -- (in ETT I never have to Transp, ass soon as Id t u is in scope, everything
                               -- happens automatically (t and u are identified in the metatheory)

- 1. informally we use ETT to write proofs which are nice because no tranports are need
   (is undecidable)

- 2. another kind of ETT notation: everything is annotated by *metatheoretic* transports
    (whenever I use Reflect, I have to mention a metatheoretic equality proof)
  (kind of notation that we get if we formalize ETT in Agda)

- conservativity: everything provable in ETT is already provable with Transp + UIP + funext
                          (refers to 2. type of objects)

- SetoidTT vs ETT   (equality proofs are unique/irelevant)
-                   (SetoidTT has a way of decidable/systematic computation/elimination of Transp)
-                   (ETT does not have (works by magic))

examples:

coe : (A B : Set) → Id A B → A → B     (special case of Transp)

-- nil : {A : Set} → List A
coe (List A) (List B) p (nil {A}) = nil {B}

-- Transp (n. Vec A (suc n)) (ap suc p) (cons x xs) = cons x (Transp (n. Vec A n) p xs)
-- Transp B (p : Id t u) x = x   -- only well-typed with Reflect

-- Concrete proof of undecidable equality of ETT terms
--------------------------------------------------------------------------------

idea: - I specify the rules of SK calculus (Turing-complete)
      - I put the rules into some Γ context
      - (t, u: Tm Γ SKTm)   deciding t = u requires deciding Turing-complete system

Γ = (T : U, -$- : T ⇒ T ⇒ T,
             K  : T,
             S  : T,
             Kβ : Id (K $ t $ u) t,
             Sβ : Id (S $ f $ g $ t) (f $ t $ (g $ t)))

Tm Γ T has undecidable equality  (I just have to chose any undecidable equational theory for Γ)

-- only undecidable if we have Reflect!
   - every Id proof in Γ yields a metatheoretic equality.
   - Reflect: {t u : Tm Γ T} → (p : Tm Γ (Id T t u)) → t = u
       (Reflect implies (t = u) is decidable iff (Tm Γ (Id T t u)) is decidable


-- Dependent elimination for Id
--------------------------------------------------------------------------------

dep-if-then-else : (P : Ty (Γ, Bool)) → Tm Γ (P[id, true]) → Tm Γ (P[id, false]) → (b : Tm Γ Bool)
                   → Tm Γ (P[id, b])
(induction on Bool)

Transp  : (B : Ty (Γ, A)){t u : Tm Γ A}(p : Tm Γ (Id A t u)) → Tm Γ (B[id, t]) → Tm Γ (B[id, u])
-}

-- P depends on an Id  (we want to prove something about an equality proof)
-- "If P can be proven for (refl x) then P can be proven for any p"
J : {A : Set}{x : A}(P : (y : A) → Id x y → Set) → P x refl → (y : A)(p : Id x y) → P y p
J P Prefl y refl = Prefl
-- Jβ is the pattern definition above

-- Why do we even need J?
-- If we only have refl + Transp (not UIP), is there something which is not
--    possible, but possible to define with J?

-- computationally relevant function : (a : A)(f : A → B) → f a ≡ .. → C
-- simple examples: prove something about how transport/J computes

-- show how trans computes in some cases:

trans-refl : {A : Set}{x y : A}(p : Id x y) → Id (trans refl p) p    -- sometimes I want to show that (p = refl)
                                                                     -- in that case J/Transp computes
trans-refl {A} {x}{y} p = J (λ y p → Id (Transp (Id x) p refl) p) refl y p
    -- J allows me to rewrite some (p : Id x y) to (refl x) in the goal type


-- This reason is important if we're working without UIP (in ITT)
--     (becomes more interesting if we're working homotopy type theory)
--     (HoTT: adds axioms which are incompatible with UIP)
--            axioms which allow more interesting equality proofs to be constructed
--       (e.g. two types are not only equal if they're the same, but also if they're isomorphic
--             isomorphism: back-and-forth mapping, composing to identity functions

-- (Identity types are the main point of divergence between different type theory variants)

-- Question: can we have two different Id-s?
--  (Specify two Id types)
--   Id has Transp + UIP
--   Id' has J
--   (show that Id is equivalent to Id')

-- What works: two-level type theory
--   we have two universes + a lifting construction from U0 to U1
--   Id1 in U1, with UIP
--   Id0 in U0, without UIP
--  (this works)

--  U(i, j)     i ∈ {0, 1}  (two-level TT levels)
--              j ∈ ℕ       (usual universe hierarchy)

-- if (A : U(0, i)) then (Lift A : U(1, i))
-- + every elimination principle stays in the same i-level

-- Tranps + UIP implies J
-- J does not imply UIP

-- usual use case for 2lvlTT: inner level has anti-UIP axioms, outer level has UIP
--    commonly inner: HoTT, outer: ETT

-- next time
--------------------------------------------------------------------------------

-- models other than Set (Family model? (refutation of LEM, parametricity properties))
