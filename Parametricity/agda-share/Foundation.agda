
module Foundation where

open import Data.Empty
open import Data.Product

open import Data.Nat
open import Data.Nat.Properties

open import Induction.WellFounded

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

_≥_>_ : ℕ → ℕ → ℕ → Set
k ≥ n > m = m < n × n ≤ k

≤-refl : ∀{n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

Rel' : Set → Set₁
Rel' A = Rel A _

Monotone : ∀{A B} → (_≺_ : Rel' A) (_≺'_ : Rel' B) (f : A → B) → Set
Monotone _≺_ _≺'_ f = ∀{x y} → x ≺ y → f x ≺' f y

mon-acc : ∀{A B _≺_ _≺'_} {f : A → B} {x}
        → Monotone _≺_ _≺'_ f → Acc _≺'_ (f x) → Acc _≺_ x
mon-acc mon (acc rs) = acc (λ y y≺x → mon-acc mon (rs _ (mon y≺x)))

lemma₀ : ∀ k x → k ∸ x ≤ k
lemma₀ k 0             = ≤-refl
lemma₀ zero    (suc x) = ≤-refl
lemma₀ (suc k) (suc x) = ≤-step (lemma₀ k x)

mono-∸ : ∀ k → Monotone (_≥_>_ k) _<_ (_∸_ k)
mono-∸ zero (y<x , x≤k) with DecTotalOrder.trans 
                                  Data.Nat.decTotalOrder y<x x≤k
mono-∸ zero (y<x , x≤k) | ()
mono-∸ (suc k) {zero}          (() ,      x≤k)
mono-∸ (suc k) {suc x} {zero}  (y<x ,     x≤k)     = s≤s (lemma₀ k x)
mono-∸ (suc k) {suc x} {suc y} (s≤s y<x , s≤s x≤k) 
  = mono-∸ k {x} {y} (y<x , x≤k)

acc-all : ∀ n → Acc _<_ n
acc-all n = acc (aux n)
 where
 aux : ∀ n m → m < n → Acc _<_ m
 aux zero    m       ()
 aux (suc n) zero    m<n       = acc (λ _ ())
 aux (suc n) (suc m) (s≤s m<n) = acc (λ i i<sm → aux n i (trans' i<sm m<n))
  where
  open DecTotalOrder Data.Nat.decTotalOrder renaming (trans to trans') 

bgt-acc : ∀ k n → Acc (_≥_>_ k) n
bgt-acc k n = mon-acc {_≺'_ = _<_} (mono-∸ k) (acc-all _)

