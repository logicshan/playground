{-# OPTIONS --universe-polymorphism #-}

-- Some handy types and functions in the meta-theory

module Meta where

postulate Level : Set
postulate lz : Level
postulate ls : Level → Level
postulate _⊔_ : Level → Level → Level
infixr 30 _⊔_
{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lz    #-}
{-# BUILTIN LEVELSUC  ls    #-}
{-# BUILTIN LEVELMAX _⊔_ #-}

infixl 0 _$_
_$_ : ∀{i j} {A : Set i} {B : A → Set j} → ((x : A) → B x) → (x : A) → B x
f $ x = f x

infixl 90 _∘_
_∘_ : ∀{i j k} {A : Set i} {B : A → Set j} {C : (x : A) → B x → Set k}
    → (g : {x : A} → (y : B x) → C x y)
    → (f : (x : A) → B x)
    → (x : A) → C x (f x)
(g ∘ f) x = g (f x)

_-:>_ : ∀{i j k} {I : Set i} → (I → Set j) → (I → Set k) → Set (i ⊔ j ⊔ k)
_-:>_ {I = I} S T = ∀ i → S i → T i


data ⊥ : Set where

naughty : ∀{i} {A : Set i} → ⊥ → A
naughty ()

record ⊤ : Set where

infix 20 ¬_
¬_ : ∀{i} → Set i → Set i
¬ P = P → ⊥

data Bool : Set where
  false : Bool
  true  : Bool

not : Bool → Bool
not false = true
not true  = false

if_then_else_ : ∀{i} {A : Set i} → Bool → A → A → A
if true  then t else _ = t
if false then _ else f = f

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data Fin : ℕ → Set where
  zero : ∀{n}         → Fin (suc n)
  suc  : ∀{n} → Fin n → Fin (suc n)

inj : ∀{n} → Fin n → Fin (suc n)
inj zero    = zero
inj (suc n) = suc (inj n)

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B fst

infixr 40 _,_
open Σ public

infixr 40 _×_
_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A (λ _ → B)

∃ : ∀{i j} {A : Set i} (B : A → Set j) → Set (i ⊔ j)
∃ {A = A} B = Σ A B

infixr 30 _⋀_
_⋀_ : Set → Set → Set
P ⋀ Q = P × Q

infixr 35 _⊎_
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 28 _⋁_
_⋁_ : Set → Set → Set
_⋁_ = _⊎_

data W (A : Set) (B : A → Set) : Set where
  _◂_ : (x : A) → (f : B x → W A B) → W A B

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

data _≡_ {i} {A : Set i} (x : A) : A → Set i where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

subst : ∀{i j} {A : Set i} (P : A → Set j) {x y} → x ≡ y → P x → P y
subst P refl Px = Px

cong : ∀{i j} {A : Set i} {B : Set j} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

K : ∀{i} {A : Set i} {x : A} (p : x ≡ x) → p ≡ refl
K refl = refl

module Reasoning (A : Set) where
  infix 10 begin_
  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin eq = eq

  infixr 15 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ x {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ refl ⟩ refl = refl

  infix 20 _∎
  _∎ : ∀(x : A) → x ≡ x
  _ ∎ = refl

data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
  ≅-refl : x ≅ x

≅-subst : ∀{A B : Set} (P : {C : Set} → C → Set) {x : A} {y : B} 
        → x ≅ y → P x → P y
≅-subst P ≅-refl Px = Px
