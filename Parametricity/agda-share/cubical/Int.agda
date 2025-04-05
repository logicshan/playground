
module Int where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

data ℤ : Type where
  zero : ℤ
  suc pre : ℤ -> ℤ
  s-p : ∀ i → suc (pre i) ≡ i
  p-s : ∀ i → pre (suc i) ≡ i
  squash : isSet ℤ

elim : ∀{F : ℤ -> Type}
     → (∀ i → isSet (F i))
     → F zero
     → (Fs : ∀{i} → F i -> F (suc i))
     → (Fp : ∀{i} → F i -> F (pre i))
     → (∀{i} Fi → PathP (λ τ → F (s-p i τ)) (Fs (Fp Fi)) Fi)
     → (∀{i} Fi → PathP (λ τ → F (p-s i τ)) (Fp (Fs Fi)) Fi)
     → ∀ i → F i
elim {F} Fst Fz Fs Fp Fsp Fps = go where
  Fstd : isOfHLevelDep 2 F
  Fstd = isOfHLevel→isOfHLevelDep 2 Fst

  go : ∀ i → F i
  go zero = Fz
  go (suc i) = Fs (go i)
  go (pre i) = Fp (go i)
  go (s-p i τ) = Fsp (go i) τ
  go (p-s i τ) = Fps (go i) τ
  go (squash i j p q τ σ) =
    Fstd (go i) (go j) (cong go p) (cong go q) (squash i j p q) τ σ

ind : ∀{P : ℤ -> Type}
    → (∀ i → isProp (P i))
    → P zero
    → (∀{i} → P i -> P (suc i))
    → (∀{i} → P i -> P (pre i))
    → ∀ i → P i
ind {P} Ppr Pz Ps Pp =
  elim (isProp→isSet ∘ Ppr) Pz Ps Pp
    (λ _ → Pprd _ _ (s-p _))
    (λ _ → Pprd _ _ (p-s _))
  where
  Pprd : isPropDep P
  Pprd = isOfHLevel→isOfHLevelDep 1 Ppr
