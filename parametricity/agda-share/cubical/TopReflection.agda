{-# OPTIONS --cubical --postfix-projections #-}

module TopReflection where

open import Cubical.Core.Everything

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.HITs.S1 hiding (inv)
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

variable
  ℓ : Level

data [3] : Type₀ where
  [0] [1] [2] : [3]

[0]≢[1] : ¬ [0] ≡ [1]
[0]≢[1] p = subst P p _
  where
  P : [3] → Type₀
  P [1] = ⊥
  P _ = ⊤

[0]≢[2] : ¬ [0] ≡ [2]
[0]≢[2] p = subst P p _
  where
  P : [3] → Type₀
  P [2] = ⊥
  P _ = ⊤

[1]≢[2] : ¬ [1] ≡ [2]
[1]≢[2] p = subst P p _
  where
  P : [3] → Type₀
  P [2] = ⊥
  P _ = ⊤

[3]discrete : Discrete [3]
[3]discrete [0] [0] = yes refl
[3]discrete [0] [1] = no [0]≢[1]
[3]discrete [0] [2] = no [0]≢[2]
[3]discrete [1] [0] = no ([0]≢[1] ∘ sym)
[3]discrete [1] [1] = yes refl
[3]discrete [1] [2] = no [1]≢[2]
[3]discrete [2] [0] = no ([0]≢[2] ∘ sym)
[3]discrete [2] [1] = no ([1]≢[2] ∘ sym)
[3]discrete [2] [2] = yes refl

[3]set : isSet [3]
[3]set = Discrete→isSet [3]discrete

module _ where
  open Iso

  switch : [3] → [3]
  switch [0] = [0]
  switch [1] = [2]
  switch [2] = [1]

  switch² : ∀ t → switch (switch t) ≡ t
  switch² [0] = refl
  switch² [1] = refl
  switch² [2] = refl

  Switch : [3] ≡ [3]
  Switch = isoToPath sw where
    sw : Iso [3] [3]
    sw .fun = switch
    sw .inv = switch
    sw .rightInv = switch²
    sw .leftInv = switch²

  ¬Switch[1] : ¬ transport Switch [1] ≡ [1]
  ¬Switch[1] = [1]≢[2] ∘ sym

  ¬Switch[2] : ¬ transport Switch [2] ≡ [2]
  ¬Switch[2] = [1]≢[2]

  Switch[0] : ∀ t → PathP (λ i → Switch i) t t → [0] ≡ t
  Switch[0] [0] _ = refl
  Switch[0] [1] = ⊥-elim ∘ ¬Switch[1] ∘ fromPathP
  Switch[0] [2] = ⊥-elim ∘ ¬Switch[2] ∘ fromPathP


F : S¹ → Type₀
F base = [3]
F (loop i) = Switch i

TS : Type₀
TS = Σ[ t ∈ [3] ] transport Switch t ≡ t

defunctionalize
  : (∀ c → F c)
  → Σ[ t ∈ [3] ] PathP (λ i → Switch i) t t
defunctionalize f = f base , cong f loop

functionalize
  : Σ[ t ∈ [3] ] PathP (λ i → Switch i) t t
  → ∀ c → F c
functionalize (b , l) base = b
functionalize (b , l) (loop i) = l i

functionalRetract : retract defunctionalize functionalize
functionalRetract f i base = f base
functionalRetract f i (loop j) = f (loop j)

lemma₄ : isContr TS
lemma₄ .fst = [0] , refl
lemma₄ .snd ([0] , p) = ΣPathP (refl , [3]set _ _ refl p)
lemma₄ .snd ([1] , p) = ⊥-elim (¬Switch[1] p)
lemma₄ .snd ([2] , p) = ⊥-elim (¬Switch[2] p)

lemma₅ : isContr (Σ[ t ∈ [3] ] PathP (λ i → Switch i) t t)
lemma₅ = subst (λ(R : [3] → Type₀) → isContr (Σ[ t ∈ [3] ] R t)) sub-lemma lemma₄
  where
  sub-lemma
    : Path ([3] → Type₀)
        (λ x → transport Switch x ≡ x)
        (λ x → PathP (λ i → Switch i) x x)
  sub-lemma i x = ua (toPathP {x = x} {x} , toPathP-isEquiv (λ i → Switch i)) i

lemma₆ : isContr (∀ c → F c)
lemma₆ = retractIsContr defunctionalize functionalize functionalRetract lemma₅

lemma₇ : Σ[ c ∈ S¹ ] ¬ isContr (F c)
lemma₇ .fst = base
lemma₇ .snd ([0] , ap) = [0]≢[1] (ap [1])
lemma₇ .snd ([1] , ap) = [1]≢[2] (ap [2])
lemma₇ .snd ([2] , ap) = [1]≢[2] (sym (ap [1]))
