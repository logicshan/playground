{-# OPTIONS --prop --rewriting #-}

module Nat2 where
open import Lib

record Model {ℓ} : Set (lsuc ℓ) where
  field
    Nat   : Set ℓ
    Zero  : Nat
    Suc   : Nat → Nat

  ⟦_⟧ : ℕ → Nat
  ⟦ zero ⟧ = Zero
  ⟦ suc n ⟧ = Suc ⟦ n ⟧

I : Model
I = record { Nat = ℕ ; Zero = 0 ; Suc = 1 +_ }

module I = Model I

M : Model
M = record { Nat = I.Nat ; Zero = I.Suc I.Zero ; Suc = λ n → I.Suc (I.Suc n) }

module M = Model M

testM0 : M.⟦ 0 ⟧  ≡ 1
testM1 : M.⟦ 1 ⟧  ≡ 3
testM2 : M.⟦ 2 ⟧  ≡ 5

testM0 = refl
testM1 = refl
testM2 = refl

A : Model
A = record { Nat = I.Nat → I.Nat ; Zero = λ n → n ; Suc = λ f → I.Suc ∘ f }

module A = Model A

testA0 : A.⟦ 0 ⟧  ≡ λ n → n
testA1 : A.⟦ 1 ⟧  ≡ I.Suc
testA2 : A.⟦ 2 ⟧  ≡ I.Suc ∘ I.Suc
testA3 : A.⟦ 3 ⟧  ≡ I.Suc ∘ I.Suc ∘ I.Suc

testA0 = refl
testA1 = refl
testA2 = refl
testA3 = refl

_+'_ : I.Nat → I.Nat → I.Nat
_+'_ = A.⟦_⟧

test1+3 : 1 +' 3 ≡ 4
test3+2 : 3 +' 2 ≡ 5

test1+3 = refl
test3+2 = refl

record DepModel {ℓ} : Set (lsuc ℓ) where
  field
--    Nat∙   : I.Nat → Prop ℓ
    Nat∙   : I.Nat → Set ℓ
    Zero∙  : Nat∙ I.Zero
    Suc∙   : {n : I.Nat} → Nat∙ n → Nat∙ (I.Suc n)

  ⟦_⟧ : (n : I.Nat) → Nat∙ n
  ⟦ zero ⟧ = Zero∙
  ⟦ suc n ⟧ = Suc∙ ⟦ n ⟧

Ass : (n o : I.Nat) → DepModel
Ass n o = record
  {  Nat∙   = λ m → Lift ((m +' n) +' o ≡ m +' (n +' o))
  ;  Zero∙  = mk refl
  ;  Suc∙   = λ{ (mk x) → mk (cong I.Suc x) }
  }

ass : (m n o : I.Nat) → (m +' n) +' o ≡ m +' (n +' o)
ass m n o = un Assno.⟦ m ⟧
  where
    module Assno = DepModel (Ass n o)

Identityʳ : DepModel
Identityʳ = record
  { Nat∙ = λ x → Lift (x +' I.Zero ≡ x)
  ; Zero∙ = mk refl
  ; Suc∙ = λ{ (mk x) → mk (cong I.Suc x) }
  }

identityʳ : (x : I.Nat) → (x +' I.Zero ≡ x)
identityʳ x = un Identityʳ.⟦ x ⟧
  where
    module Identityʳ = DepModel Identityʳ

+Suc' : (y : I.Nat) → DepModel
+Suc' y = record
  { Nat∙ = λ x → Lift (x +' (I.Suc y) ≡ I.Suc (x +' y))
  ; Zero∙ = mk refl
  ; Suc∙ = λ{ (mk x) → mk (cong I.Suc x) }
  }

+suc' : (x y : I.Nat) → x +' (suc y) ≡ suc (x +' y)
+suc' x y = un +Suc'.⟦ x ⟧
  where
    module +Suc' = DepModel (+Suc' y)

Comm : (y : I.Nat) → DepModel
Comm y = record
  { Nat∙ = λ x → Lift (x +' y ≡ y +' x)
  ; Zero∙ = mk (identityʳ (I.Zero +' y) ⁻¹)
  ; Suc∙ = λ {x} (mk p) → mk (cong I.Suc p ◾ (+suc' y x) ⁻¹)
  }

comm : (x y : I.Nat) → x +' y ≡ y +' x
comm x y = un Comm.⟦ x ⟧
  where
    module Comm = DepModel (Comm y)

suc≠zero' : ∀ {i} → ¬ (I.Suc i ≡ I.Zero)
suc≠zero' = λ ()

SucInj : DepModel
SucInj = record
  { Nat∙ = λ _ → I.Nat
  ; Zero∙ = zero
  ; Suc∙ = λ {n} x → I.Suc x
  }

SucInj' : Model
SucInj' = record
  { Nat = I.Nat
  ; Zero = I.Zero
  ; Suc = λ n → n
  }

sucInj : ∀{n n'} → I.Suc n ≡ I.Suc n' → n ≡ n'
sucInj e = cong SucInj.⟦_⟧ {!e!}
  where
  module SucInj = DepModel SucInj
