
module WeirdSetoid where

open import Data.Bool
open import Data.Bool.Properties
open import Data.Unit
open import Function.Equality
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid; IsIndexedEquivalence)
open import Relation.Binary.PropositionalEquality
  as PE using (_≡_)
open import Relation.Nullary

open Setoid
open IndexedSetoid
open IsEquivalence
open IsIndexedEquivalence

𝟙 : Setoid _ _
𝟙 .Carrier = Bool
𝟙 ._≈_ _ _ = ⊤
𝟙 .isEquivalence = λ where
    .refl → tt
    .sym tt → tt
    .trans tt tt → tt

𝟚 : Setoid _ _
𝟚 .Carrier = Bool
𝟚 ._≈_ b c = b ≡ c
𝟚 .isEquivalence = PE.isEquivalence

Weird : IndexedSetoid Bool _ _
Weird .Carrier _ = Bool
Weird ._≈_ {i} {j} _ _ = i ≡ j
Weird .isEquivalence = λ where
  .refl → PE.refl
  .sym → PE.sym
  .trans → PE.trans

lemma₀ : ¬ Π 𝟙 Weird
lemma₀ f with f .cong {false} {true} tt
... | ()

lemma₁ : Π 𝟚 Weird
lemma₁ ._⟨$⟩_ b = b
lemma₁ .cong e = e

cover : 𝟚 ⟶ 𝟙
cover ._⟨$⟩_ b = b
cover .cong _ = tt
