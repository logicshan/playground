
module CountableMPEM where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary


-- A is a subtype of ℕ
record Subℕ (A : Type) : Type where
  field
    f : A -> ℕ
    f-inj : ∀(x y : A) → f x ≡ f y -> x ≡ y

-- ℕ covers A; A is countably enumerable
record ℕCov (A : Type) : Type where
  field
    g : ℕ -> Maybe A
    g-sur : ∀ x → ∥ fiber g (just x) ∥₁

open Subℕ

-- Markov's Principle
MP : Type₁
MP = ∀{Q : ℕ -> Type}
   → (∀ n → isProp (Q n))
   → (∀ n → Dec (Q n))
   → ¬ ¬ Σ ℕ Q
   → Σ ℕ Q

module _
  -- Suppose every subtype of A were countably enumerable
  (hyp : ∀{A} → Subℕ A -> ℕCov A)
  (P : Type)
  (Pp : isProp P)
  where
  -- Dec P is a subtype of ℕ
  ST : Subℕ (Dec P)
  ST .f x = 0
  ST .f-inj p q _ = isPropDec Pp p q

  -- So it must be countably enumerable
  CT : ℕCov (Dec P)
  CT = hyp ST

  open ℕCov CT

  is-just : ∀{A : Type} → Maybe A -> Type
  is-just (just _) = Unit
  is-just nothing = ⊥

  -- Q is our search predicate; we will look for `just` results in the
  -- enumeration.
  Q : ℕ -> Type
  Q n = is-just (g n)

  -- Q is propositional ...
  Qp : ∀ n → isProp (Q n)
  Qp n with g n
  ... | nothing = isProp⊥
  ... | just  _ = isPropUnit

  -- ... and decidable.
  Qd : ∀ n → Dec (Q n)
  Qd n with g n
  ... | nothing = no (idfun ⊥)
  ... | just  _ = yes _

  -- A just value of g lets us decide P
  lemma₁ : ∀ n → is-just (g n) -> Dec P
  lemma₁ n j with g n
  ... | just p = p

  -- Q cannot always be false
  lemma₂ : ¬ ¬ Σ ℕ Q
  lemma₂ k = sub₂ sub₁ where
    -- If it were, then every fiber over just would be empty.
    sub₀ : ∀ x → ¬ fiber g (just x)
    sub₀ x (n , p) = k (n , subst⁻ is-just p _)

    -- So we could refute P ...
    sub₁ : ¬ P
    sub₁ p = PT.rec isProp⊥ (sub₀ _) (g-sur (yes p))

    -- ... and refute ¬ P ...
    sub₂ : ¬ ¬ P
    sub₂ ¬p = PT.rec isProp⊥ (sub₀ _) (g-sur (no ¬p))

    -- ... which is impossible by non-contradiction

  -- So by Markov's principle, we will find a just, which allows us
  -- to decide P.
  MP->EM : MP -> Dec P
  MP->EM mp = uncurry lemma₁ (mp Qp Qd lemma₂)

