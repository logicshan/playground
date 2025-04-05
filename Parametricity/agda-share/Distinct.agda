
module Distinct where

data ⊥ : Set where

infix 40 ¬_
¬_ : Set → Set
¬ A = A → ⊥

record ⊤ : Set where

infix 50 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- equality elimination
J : ∀{A : Set}{x y : A} (P : A → Set) → x ≡ y → P x → P y
J P refl Px = Px

-- all proofs of x ≡ x are refl, but we don't need that
K : ∀{A : Set}{x : A}{P : x ≡ x → Set} → P refl → (pf : x ≡ x) → P pf
K Prefl refl = Prefl

data Bool : Set where
  true  : Bool
  false : Bool

-- large Bool elimination
Case : ∀ T U → Bool → Set
Case T _ true  = T
Case _ U false = U

-- Bool elimination
case : ∀{T U} → T → U → (b : Bool) → Case T U b
case t _ true  = t
case _ u false = u

-- the stuff above would be available primitively

t≢f : ¬ true ≡ false
t≢f t≡f = case {⊤} {⊥} _ (J T t≡f _) false
 where
 T : Bool → Set
 T = Case ⊤ ⊥
