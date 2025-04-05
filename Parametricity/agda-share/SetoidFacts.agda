
module SetoidFacts where

open import Level
open import Function hiding (_⟶_; _⟨_⟩_)
open import Function.Equality using (_⟶_; _⟨$⟩_; _⇨_) renaming (setoid to Π)
open import Data.Product
open import Data.Unit
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PE
open PE hiding (isEquivalence)

variable
  ℓ c d r s : Level
  A : Set c
  S : Setoid c r

-- Nicer notation for carrier of a setoid
⟨_⟩ : Setoid c r -> Set c
⟨_⟩ = Setoid.Carrier

-- Equip a type with its equality to make a setoid.
△_ : Set c -> Setoid c c
(△ A) .Setoid.Carrier = A
(△ A) .Setoid._≈_ = _≡_
(△ A) .Setoid.isEquivalence = PE.isEquivalence

-- For any setoid, there is a setoid consisting of its carrier
-- equipped with equality. These make up a special class of setoids.
□_ : Setoid c r -> Setoid c c
□ A = △ Setoid.Carrier A

-- A setoid is covered by its setoid of carriers.
module Cover (S : Setoid c r) where
  module S = Setoid S
  open S
  open IsEquivalence isEquivalence

  cover : □ S ⟶ S
  cover ._⟨$⟩_ = id
  cover .Function.Equality.cong refl = S.refl

  -- This should be understood as witnesses for the setoid
  -- proposition. Actually defining the setoids for the formula would
  -- add a lot of boilerplate.
  is-cover : ∀ y → ∃[ x ] (cover ⟨$⟩ x ≈ y)
  is-cover y = y , S.refl

-- □ is idempotent
idem : □ □ S ≡ □ S
idem = refl

-- A setoid is a proposition if all its carrier elements are related.
isProp : Setoid c r -> Set _
isProp P = ∀(p q : ⟨P⟩) → p ≈ q where
  open Setoid P renaming (Carrier to ⟨P⟩)

-- The always true equivalence is an equivalence
triv-equiv : IsEquivalence {A = A} (λ _ _ → ⊤)
triv-equiv .IsEquivalence.refl = _
triv-equiv .IsEquivalence.sym _ = _
triv-equiv .IsEquivalence.trans _ _ = _

-- The setoid of level ℓ propositions
--
-- Every proposition is isomorphic to a proposition with a level 0
-- relation, so making that restriction doesn't really matter and
-- saves a level variable.
Ω : (ℓ : Level) -> Setoid (suc ℓ) _
Ω ℓ .Setoid.Carrier = Σ (Setoid ℓ zero) isProp
Ω ℓ .Setoid._≈_ (P , _) (Q , _) = (⟨ P ⟩ -> ⟨ Q ⟩) × (⟨ Q ⟩ -> ⟨ P ⟩)
Ω ℓ .Setoid.isEquivalence = λ where
  .IsEquivalence.refl → id , id
  .IsEquivalence.sym (f , g) → g , f
  .IsEquivalence.trans (f0 , g0) (f1 , g1) → (f1 ∘ f0) , (g0 ∘ g1)

-- Propositional truncation, simultaneously reducing the relation level.
∥_∥₁ : Setoid c r -> Setoid c zero
∥ A ∥₁ .Setoid.Carrier = ⟨ A ⟩
∥ A ∥₁ .Setoid._≈_ _ _ = ⊤
∥ A ∥₁ .Setoid.isEquivalence = triv-equiv

-- Isomorphism of setoids.
_≅_ : Setoid c r -> Setoid d s -> Set _
A ≅ B = Inverse A B

-- Every proposition is isomorphic to its truncation, which has a
-- potentially smaller relation level.
resized : ∀(A : Setoid c r) → isProp A -> A ≅ ∥ A ∥₁
resized A Ap .Inverse.to = id
resized A Ap .Inverse.from = id
resized A Ap .Inverse.to-cong _ = _
resized A Ap .Inverse.from-cong _ = Ap _ _
resized A Ap .Inverse.inverse .proj₁ _ = _
resized A Ap .Inverse.inverse .proj₂ _ = Ap _ _

-- A variant of choice that is relatively easy to state (no
-- dependency).  Essentially the same thing will work if we use a Π
-- setoid instead of _⇨_, but there is much more boilerplate.
--
-- You get more familiar versions of the axiom of choice by choosing Σ
-- setoids for B. Those of course also incur setoid boilerplate for
-- the families of types. Note also that even this would be simplified
-- by the fact that choice is holding for △ A, which are trivial
-- setoids that make the stdlib's IndexedSetoid a valid notion of a
-- family of setoids over △ A. For an arbitrary setoid A, a family of
-- setoids over A would have to satisfy additional coherence
-- conditions about the fibers.
choice : {A : Set ℓ} {B : Setoid c r} -> (△ A ⇨ ∥ B ∥₁) ⟶ ∥ △ A ⇨ B ∥₁
(choice ⟨$⟩ f) ⟨$⟩ x = f ⟨$⟩ x
(choice {A = A} {B} ⟨$⟩ f) .Function.Equality.cong refl
  = IsEquivalence.refl (B .Setoid.isEquivalence)
choice .Function.Equality.cong _ = _

-- This makes setoids satisfy the 'presentation axiom.' Every setoid S
-- is covered by a setoid □S that satisfies the axiom of choice. This
-- is because choice for □S is just the normal type theoretic ΠΣ→ΣΠ
-- manipulation, because □S has canoncal representatives up to
-- propositional equality. Every x : □S corresponds to a unique y : ⟨B⟩
-- up to underlying equality. Different ΠΣ inputs yield different ΣΠ
-- functions, but that doesn't matter because the truncation crushes
-- them all together.
--
-- This happens for _every_ setoid. So, for instance, the axiom of
-- choice does not hold constructively for A ⇨ B in general, but holds
-- for □(A ⇨ B) = △(A ⟶ B), the setoid of setoid-functions up to
-- underlying propositional equality. Or for instance, for the Cauchy
-- reals ℝ, □ℝ is the setoid of Cauchy sequences up to the same
-- function equality. Note that this is _very_ weak, though, because
-- in Agda, even two sequences that agree on every approximation might
-- not be provably equal.
