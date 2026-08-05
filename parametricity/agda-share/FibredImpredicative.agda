{-# OPTIONS --type-in-type #-}

module FibredImpredicative where

open import Function

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality

-- A very incomplete demonstration of type schemes, universal and
-- existential quantification inspired vaguely by the fibred category approach.

-- A type schema in n free type variables is an object of Fam n
Fam : ℕ → Set₁
Fam n = Vec Set n → Set

-- The category of types is isomorphic to Fam 0 in the obvious way
↑ : Set → Fam 0
↑ A = const A

↓ : Fam 0 → Set
↓ F = F []

-- Weakening of families. We can take a schema in n variables and produce
-- a schema in n+1 variables that doesn't contain the new variable
Δ : ∀ n → Fam n → Fam (suc n)
Δ n F Vs = F (tail Vs)

-- type-in-type should only be used for the following two definitions to
-- simulate impredicativity

-- In an impredicative system, we can quantify over a type variable in a
-- schema in two ways, universally...
∀̂ : ∀ n → Fam (suc n) → Fam n
∀̂ n F Vs = ∀ V → F (V ∷ Vs)

-- ... and existentially.
∃̂ : ∀ n → Fam (suc n) → Fam n
∃̂ n F Vs = Σ[ V ∶ Set ] F (V ∷ Vs)

-- Morphisms of schemas are uniform families of functions, although the
-- uniformity is implicitly enforced here, not really proved.
infixr 10 _⇉_
_⇉_ : ∀{n} → Fam n → Fam n → Set
F ⇉ G = ∀ Vs → F Vs → G Vs

-- We have point-wise products.
infixr 20 _×̂_
_×̂_ : ∀{n} → Fam n → Fam n → Fam n
F ×̂ G = λ vs → F vs × G vs

-- And proposed exponentials.
_^̂_ : ∀{n} → Fam n → Fam n → Fam n
G ^̂ F = λ vs → F vs → G vs

-- lo and behold
♯₀ : ∀ n (F G H : Fam n) → (F ×̂ G ⇉ H) → (F ⇉ H ^̂ G)
♯₀ n F G H f = λ Vs x y → f Vs (x , y)

♭₀ : ∀ n (F G H : Fam n) → (F ⇉ H ^̂ G) → (F ×̂ G ⇉ H)
♭₀ n F G H g = λ Vs p → g Vs (proj₁ p) (proj₂ p)

lemma : ∀ n (Vs : Vec Set (suc n)) → Vs ≡ head Vs ∷ tail Vs
lemma n (V ∷ Vs) = refl

-- ∃̂ n ⊣ Δ n
♯₁ : ∀ n F G → (∃̂ n F ⇉ G) → (F ⇉ Δ n G)
♯₁ n F G f = λ Vs FVs → f (tail Vs) (head Vs , subst F (lemma n Vs) FVs)

♭₁ : ∀ n F G → (F ⇉ Δ n G) → (∃̂ n F ⇉ G)
♭₁ n F G g = λ Vs VFVs → g (proj₁ VFVs ∷ Vs) (proj₂ VFVs)

-- Δ n ⊣ ∃̂ n
♯₂ : ∀ n F G → (Δ n F ⇉ G) → (F ⇉ ∀̂ n G)
♯₂ n F G f = λ Vs FVs V → f (V ∷ Vs) FVs

♭₂ : ∀ n F G → (F ⇉ ∀̂ n G) → (Δ n F ⇉ G)
♭₂ n F G g = λ Vs FtVs → subst G (sym (lemma n Vs)) (g (tail Vs) FtVs (head Vs))

-- isomorphism and naturality left as an exercise for the reader