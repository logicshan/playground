{-# OPTIONS --lossy-unification #-}

module TrivMLTT where

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

import Data.Empty as Empty
import Data.Product as Product
import Data.Nat as Nat
import Data.Sum as Sum
import Data.Unit as Unit
import Data.W as W
import Data.Container as W

-- A model of Martin-löf type theory without universes
record Model ℓ ℓ' : Set (ℓ-suc (ℓ ⊔ ℓ')) where
  field
    Type : Set ℓ
    Val : Type -> Set ℓ'

  Fam : Type -> Set _
  Fam A = Val A -> Type

  field
    ⊥ : Type
    ⊥-elim : ∀(M : Fam ⊥) -> (b : Val ⊥) -> Val (M b)

    ⊤ : Type
    tt : Val ⊤
    ⊤-elim : ∀(M : Fam ⊤)
          -> Val (M tt)
          -> ∀ t → Val (M t)
    ⊤-elim-tt : ∀ M u → ⊤-elim M u tt ≡ u

    ℕ : Type
    zero : Val ℕ
    suc : Val ℕ -> Val ℕ
    ℕ-elim : ∀(M : Fam ℕ)
          -> Val (M zero)
          -> (∀ n → Val (M n) -> Val (M (suc n)))
          -> ∀ n → Val (M n)
    ℕ-elim-z : ∀ M z s → ℕ-elim M z s zero ≡ z
    ℕ-elim-s : ∀ M z s n → ℕ-elim M z s (suc n) ≡ s n (ℕ-elim M z s n)

    _+_ : Type -> Type -> Type
    inl : ∀{A B} → Val A -> Val (A + B)
    inr : ∀{A B} → Val B -> Val (A + B)
    +-elim : ∀{A B} (M : Fam (A + B))
          -> (∀ a → Val (M (inl a)))
          -> (∀ b → Val (M (inr b)))
          -> ∀ s → Val (M s)
    +-elim-l : ∀{A B} M l r a → +-elim {A} {B} M l r (inl a) ≡ l a
    +-elim-r : ∀{A B} M l r b → +-elim {A} {B} M l r (inr b) ≡ r b

    Σ : (A : Type) -> Fam A -> Type
    _,_ : ∀{A B} → (x : Val A) -> Val (B x) -> Val (Σ A B)
    Σ-elim : ∀{A B} (M : Fam (Σ A B))
          -> (∀ x y → Val (M (x , y)))
          -> ∀ p → Val (M p)
    Σ-elim-, : ∀{A B} M f x y → Σ-elim {A} {B} M f (x , y) ≡ f x y

    Π : (A : Type) -> Fam A -> Type
    lam : ∀{A B} → ((x : Val A) -> Val (B x)) -> Val (Π A B)
    app : ∀{A B} → Val (Π A B) -> (x : Val A) -> Val (B x)
    app-lam : ∀{A B} f x → app {A} {B} (lam f) x ≡ f x

    W : (A : Type) -> Fam A -> Type
    sup : ∀{A B} → (x : Val A) -> (Val (B x) -> Val (W A B)) -> Val (W A B)
    elim-W : ∀{A B} (M : Fam (W A B))
          -> (∀ x f -> (∀ y → Val (M (f y))) -> Val (M (sup x f)))
          -> ∀ w → Val (M w)
    elim-W-s : ∀{A B} M s x f
             → elim-W {A} {B} M s (sup x f) ≡ s x f λ y → elim-W M s (f y)

    I : (A : Type) -> Val A -> Val A -> Type
    rf : ∀{A} (x : Val A) -> Val (I A x x)
    I-elim : ∀{A x} (M : ∀ y → Fam (I A x y))
          -> Val (M x (rf x))
          -> ∀ y e → Val (M y e)
    I-elim-r : ∀{A x} M r → I-elim {A} M r x (rf x) ≡ r

  infixr 0 _=>_
  _=>_ : Type -> Type -> Type
  A => B = Π A (λ _ → B)

-- We can get the usual model by taking Types to be Sets
module Standard where
  open Model

  ST : Model _ _
  ST .Type = Set
  ST .Val A = A

  ST .⊥ = Empty.⊥
  ST .⊥-elim M b = Empty.⊥-elim b

  ST .⊤ = Unit.⊤
  ST .tt = Unit.tt
  ST .⊤-elim _ x _ = x
  ST .⊤-elim-tt _ _ = refl

  ST .ℕ = Nat.ℕ
  ST .zero = Nat.zero
  ST .suc = Nat.suc
  ST .ℕ-elim M z s Nat.zero = z
  ST .ℕ-elim M z s (Nat.suc n) = s n (ST .ℕ-elim M z s n)
  ST .ℕ-elim-z M z s = refl
  ST .ℕ-elim-s M z s n = refl

  ST ._+_ = Sum._⊎_
  ST .inl = Sum.inj₁
  ST .inr = Sum.inj₂
  ST .+-elim M = Sum.[_,_]
  ST .+-elim-l M l r a = refl
  ST .+-elim-r M l r b = refl

  ST .Σ = Product.Σ
  ST ._,_ = Product._,_
  ST .Σ-elim M = Product.uncurry
  ST .Σ-elim-, M f x y = refl

  ST .Π A B = (x : A) -> B x
  ST .lam = id
  ST .app = id
  ST .app-lam f x = refl

  ST .W A B = W.W (A W.▷ B)
  ST .sup x f = W.sup (x Product., f)
  ST .elim-W M h w = W.induction M (λ sub → h _ _ (W.□.proof sub)) w
  ST .elim-W-s M s x f = refl

  ST .I _ = _≡_
  ST .rf _ = refl
  ST .I-elim M r y e = J M e r
  ST .I-elim-r M r = refl

module _ where
  open Model

  -- The types of the trivial model, either empty or inhabited.
  data Ty : Set where
    T0 T1 : Ty

  data Va : Ty -> Set where
    va : Va T1
  
  ~_ : Ty -> Ty
  ~ T0 = T1
  ~ T1 = T0

  ~! : ∀{B} → (Va B -> Va (~ B)) -> Va (~ B)
  ~! {T0} f = va
  ~! {T1} f with f va
  ... | ()

  ~∧ : ∀{B} {A : Set} → Va B -> Va (~ B) -> A
  ~∧ {T1} _ ()

  -- The master lemma. Every value of every type is equal
  lemma : ∀ ty → (x y : Va ty) → x ≡ y
  lemma T1 va va = refl

  TM : Model _ _
  TM .Type = Ty
  TM .Val = Va

  TM .⊥ = T0

  TM .⊤ = T1
  TM .tt = va
  TM .⊤-elim M x va = x
  TM .⊤-elim-tt M u = refl

  TM .ℕ = T1
  TM .zero = va
  TM .suc _ = va
  TM .ℕ-elim M z s va = z
  TM .ℕ-elim-z M z s = refl
  TM .ℕ-elim-s M z s n = lemma (M va) z (s n _)

  TM ._+_ T0 T0 = T0
  TM ._+_ _  _  = T1
  TM .inl {T1} {T0} _ = va
  TM .inl {T1} {T1} _ = va
  TM .inr {T1} {T1} _ = va
  TM .inr {T0} {T1} _ = va
  TM .+-elim {T0} {T1} M l r va = r va
  TM .+-elim {T1} {T0} M l r va = l va
  TM .+-elim {T1} {T1} M l r va = l va
  TM .+-elim-l M l r s = lemma _ _ _
  TM .+-elim-r M l r b = lemma _ _ _

  TM .Σ T0 B = T0
  TM .Σ T1 B = B va
  TM ._,_ {T1} va x = x
  TM .Σ-elim {T1} {B} M f p = f va p
  TM .Σ-elim-, M f x y = lemma _ _ _

  TM .Π T0 B = T1
  TM .Π T1 B = B va
  TM .lam {T0} _ = va
  TM .lam {T1} f = f va
  TM .app {T1} f va = f
  TM .app-lam {T1} f va = refl

  TM .W T0 _ = T0
  TM .W T1 B = ~ B va
  TM .sup {T1} va f = ~! f
  TM .sup {T0} x f = x
  TM .elim-W {T1} M h w =
    subst (Va ∘ M) (lemma _ _ _) (h va (const w) (λ y → ~∧ y w))
  TM .elim-W-s M s x f = lemma _ _ _

  TM .I T1 x y = T1
  TM .rf {T1} x = va
  TM .I-elim {T1} {va} M r va va = r
  TM .I-elim-r M r = lemma _ _ _

module Indistinct where
  open Model TM

  -- In the trivial model we cannot show that 0 is distinct from other numbers
  indistinct-ℕ : ∀ n → ¬ Val (I ℕ zero (suc n) => ⊥)
  indistinct-ℕ n ()

  -- and we cannot show that left and right injections are distinct
  indistinct-+ : ∀{A B} x y → ¬ Val (I (A + B) (inl x) (inr y) => ⊥)
  indistinct-+ {T1} {T1} _ _ ()
  indistinct-+ {T0} ()
