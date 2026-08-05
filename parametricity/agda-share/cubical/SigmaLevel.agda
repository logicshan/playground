{-# OPTIONS --cubical --safe --no-import-sort --postfix-projections #-}

module SigmaLevel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

variable
  ℓ : Level
  A : Type ℓ
  B : A → Type ℓ

ΣPath : (p q : Σ A B) → Type _
ΣPath {B = B} (w , y) (x , z) = Σ[ p ∈ w ≡ x ] PathP (λ i → B (p i)) y z

Σctr : isContr A → isOfHLevelDep 0 B → isContr (Σ A B)
Σctr Actr Bctr .fst .fst = Actr .fst
Σctr Actr Bctr .fst .snd = Bctr .fst
Σctr Actr Bctr .snd (x , y) i .fst = Actr .snd x i
Σctr Actr Bctr .snd (x , y) i .snd = Bctr .snd y (Actr .snd x) i

Σprp : isProp A → isOfHLevelDep 1 B → isProp (Σ A B)
Σprp Aprp Bprp x y i .fst = Aprp (fst x) (fst y) i
Σprp Aprp Bprp x y i .snd = Bprp (snd x) (snd y) (Aprp (fst x) (fst y)) i

HLevelΣ
  : ∀ n → isOfHLevel n A → isOfHLevelDep n B → isOfHLevel n (Σ A B)
HLevelΣ zero = Σctr
HLevelΣ (suc zero) = Σprp
HLevelΣ {A = A} {B = B} (suc (suc n)) Alvl Blvl (w , y) (x , z)
  = transport (λ i → isOfHLevel (suc n) (ΣP≡PΣ i))
      (HLevelΣ (suc n) (Alvl w x) (Blvl y z))
  where
  ΣP≡PΣ = ΣPath≡PathΣ {A = λ _ → A} {B = λ _ → B} {x = (w , y)} {y = (x , z)}
