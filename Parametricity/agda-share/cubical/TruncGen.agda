module TruncGen where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

module Set
  (A B : Type)
  (Bset : isSet B)
  (f : A → B)
  (2k : 2-Constant f)
  where
  T : B → Type
  T y = ∀ x → f x ≡ y

  Tprop : isOfHLevelDep 1 T
  Tprop z = isOfHLevel→isOfHLevelDep 1 (λ y → isPropΠ λ x → Bset (f x) y) z

  D : Type
  D = Σ B T

  Dprop0 : A → isProp D
  Dprop0 x (y , ay) (z , az) = ΣPathP (p , Tprop ay az p)
    where
    p : y ≡ z
    p = sym (ay x) ∙ az x

  Dprop : ∥ A ∥ → isProp D
  Dprop = PT.rec isPropIsProp Dprop0

  f' : A → D
  f' x = f x , λ w → 2k w x

  res : ∥ A ∥ → B
  res x = fst (PT.rec (Dprop x) f' x)

module Gpd
  (A B : Type)
  (Bgpd : isGroupoid B)
  (f : A → B)
  (3k : 3-Constant f)
  where
  open 3-Constant
  T : B → Type
  T y = ∀ x → f x ≡ y

  Tset : isOfHLevelDep 2 T
  Tset y = isOfHLevel→isOfHLevelDep 2 (λ y → isSetΠ λ x → Bgpd (f x) y) y

  D : Type
  D = Σ B T

  Dset0 : A → isSet D
  Dset0 x (y , ay) (z , az) q r i j = λ where
      .fst → lem₀ i j
      .snd → Tset ay az (cong snd q) (cong snd r) lem₀ i j
    where
    lem₀ : cong fst q ≡ cong fst r
    lem₀ i j = hcomp (λ where
        k (j = i0) → ay x k
        k (i = i0) → q j .snd x k
        k (i = i1) → r j .snd x k
        k (j = i1) → az x k)
      (f x)

  Dset : ∥ A ∥ → isSet D
  Dset = PT.rec isPropIsSet Dset0

  f' : A → D
  f' x = f x , λ w → 3k .link w x

  --            link w x
  --         f w ------ f x
  --          |          |
  -- link w z |          | link x z
  --          |          |
  --         f z ====== f z
  2k : 2-Constant f'
  2k w x = ΣPathP (3k .link w x , λ i z → 3k .coh₁ z w x i)

  res : ∥ A ∥ → B
  res x = fst (Set.res A D (Dset x) f' 2k x)
