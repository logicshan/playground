{-# OPTIONS --cubical --postfix-projections #-}

module IQ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.Interval

! : Interval → Interval
! zero = one
! one  = zero
! (seg i) = seg (~ i)

data I/! : Set where
  inc  : Interval → I/!
  swap : ∀ i → inc i ≡ inc (! i)
  trunc : isSet I/!

lemma₁ : ∀ ι → zero ≡ ι
lemma₁ zero = refl
lemma₁ one  = seg
lemma₁ (seg i) j = seg (i ∧ j)

lemma₂ : ∀ ι → ι ≡ ! ι
lemma₂ zero = seg
lemma₂ one  = sym seg
lemma₂ (seg i) j
  = hcomp (λ k → λ where
        (i = i0) → seg j
        (i = i1) → seg (~ j ∨ ~ k)
        (j = i0) → seg i
        (j = i1) → seg (~ i ∨ ~ k))
      (seg (i ∨ j))

lemma₃ : ∀ ι → PathP (λ i → lemma₁ ι i ≡ lemma₁ (! ι) i) refl (lemma₂ ι)
lemma₃ ι i j = lemma₁ (lemma₂ ι j) i

ctr : ∀ x → inc zero ≡ x
ctr (inc ι) = cong inc (lemma₁ ι)
ctr (swap ι i) j
  = hcomp (λ k → λ where
        (i = i0) → inc (lemma₁ ι j)
        (i = i1) → inc (lemma₁ (! ι) j)
        (j = i0) → inc zero
        (j = i1) → trunc (inc ι) (inc (! ι))
                     (cong inc (lemma₂ ι))
                     (swap ι) k i)
      (inc (lemma₃ ι j i))
ctr (trunc x y p q i j) k
  = isGroupoid→isGroupoid' (hLevelSuc 2 I/! trunc)
      (λ i j → ctr x i)
      (λ i j → ctr (p j) i)
      (λ i j → ctr (q j) i)
      (λ i j → ctr y i)
      (λ _ _ → inc zero)
      (trunc x y p q)
      k i j

isContr-I/! : isContr I/!
isContr-I/! = inc zero , ctr
