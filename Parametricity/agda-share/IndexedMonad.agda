{-# OPTIONS --universe-polymorphism #-}

module IndexedMonad where

open import Level

record _×_ {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B

open _×_

IM : ∀{ℓ} → (I : Set ℓ) → Set (suc zero ⊔ ℓ)
IM I = I → I → Set → Set

record Monad {ℓ} (I : Set ℓ) (T : IM I) : Set (suc ℓ) where
  field
    return : ∀{i A} → A → T i i A
    _>>=_  : ∀{i j k A B} → T i j A → (A → T j k B) → T i k B

StateMonad : Monad Set (λ S T A → S → T × A)
StateMonad = record { return = λ x s → (s , x)
                    ; _>>=_  = λ f g s → let p = f s in g (snd p) (fst p) 
                    }

IT : ∀{ℓ ℓ'} (I : Set ℓ) → Set (suc zero ⊔ ℓ ⊔ suc ℓ')
IT {ℓ} {ℓ'} I = (J : Set ℓ') → IM J → IM (I × J)

record Trans {ℓ ℓ'} (I : Set ℓ) (TT : IT I) : Set (suc ℓ ⊔ suc ℓ') where
  field
    up : ∀{J : Set ℓ'} {T : J → J → Set → Set} {i j k A}
       → Monad J T
       → T i j A → TT J T (k , i) (k , j) A

ST : ∀{ℓ} → IT {_} {ℓ} Set
ST J T p q A = fst p → T (snd p) (snd q) (fst q × A)

StateTrans : ∀{ℓ} → Trans {_} {ℓ} Set ST
StateTrans {ℓ} = record { up = upState }
 where
 upState : ∀{J : Set ℓ} {T : IM J} {i j k A}
         → Monad J T → T i j A → k → T i j (k × A)
 upState MN m s = m >>= λ x → return (s , x)
  where
  open Monad MN


StateTransMonad : ∀{ℓ} {J : Set ℓ} {T : IM J} 
                → Monad J T → Monad (Set × J) (ST J T)
StateTransMonad {ℓ} MN = record { return = λ x → up MN (return x)
                                ; _>>=_  = λ m f s → m s >>= λ p →
                                                     f (snd p) (fst p)
                                }
 where
 open Monad MN
 open Trans (StateTrans {ℓ})
