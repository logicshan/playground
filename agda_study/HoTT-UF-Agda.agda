{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module HoTT-UF-Agda where

open import Universes public

variable
  𝓤 𝓥 𝓦 𝓣 : Universe

data 𝟙 : 𝓤₀ ̇  where
  ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇) → B → 𝟙 → B
𝟙-recursion B b = 𝟙-induction (λ _ → B) b

!𝟙' : (X : 𝓤 ̇) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤 ̇) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇) → 𝟘 → A
𝟘-recursion A = 𝟘-induction (λ _ → A)

!𝟘 : (A : 𝓤 ̇) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 ̇)
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n

ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h 0        = a₀
  h (succ n) = f n (h n)

ℕ-recursion : (X : 𝓤 ̇)
            → X
            → (ℕ → X → X)
            → ℕ → X

ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇)
            → X
            → (X → X)
            → ℕ → X

ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

module Arithmetic where

  _+_  _×_ : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 20 _+_
  infixl 21 _×_

module Arithmetic' where

  _+_  _×_ : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ

  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 20 _+_
  infixl 21 _×_

data _+_ {𝓤 𝓥} (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇  where
  inl : X → X + Y
  inr : Y → X + Y

+-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X + Y → 𝓦 ̇)
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y) → A z

+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} → (X → A) → (Y → A) → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : (A : 𝟚 → 𝓤 ̇) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

𝟚-induction' : (A : 𝟚 → 𝓤 ̇) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A
                         (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                         (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)

record Σ {𝓤 𝓥} {X : 𝓤 ̇} (Y : X → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇  where
  constructor
   _,_
  field
   x : X
   y : Y x

pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A (x , y))
            → ((x , y) : Σ Y) → A (x , y)

Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → A (x , y))
      → ((x : X) (y : Y x) → A (x , y))

curry f x y = f (x , y)

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {X : 𝓤 ̇ } → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇) → X → X
𝑖𝑑 X = id

_∘_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)

g ∘ f = λ x → g (f x)

domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇} → X → 𝓤 ̇
type-of {𝓤} {X} x = X

data Id {𝓤} (X : 𝓤 ̇) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x

_＝_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ＝ y = Id _ x y

𝕁 : (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ＝ y) → A x y p

𝕁 X A f x x (refl x) = f x

ℍ : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇ )
  → B x (refl x)
  → (y : X) (p : x ＝ y) → B y p

ℍ x B b x (refl x) = b

𝕁' : (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ＝ y) → A x y p

𝕁' X A f x = ℍ x (A x) (f x)

𝕁s-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ＝ y)
             → 𝕁 X A f x y p ＝ 𝕁' X A f x y p

𝕁s-agreement X A f x x (refl x) = refl (f x)

-- https://www.cse.chalmers.se/~coquand/singl.pdf
module 𝕁→ℍ where
  Singl : (A : 𝓤 ̇) → (x : A) → 𝓤 ̇
  Singl A x = Σ y ꞉ A , Id A x y

  J : {A : 𝓤 ̇}
    → (C : (Π x ꞉ A , Π y ꞉ A , Π p ꞉ (Id _ x y) , 𝓥 ̇))
    → (d : (Π x ꞉ A , C x x (refl x)))
    → (Π x ꞉ A , Π y ꞉ A , Π p ꞉ (Id _ x y) , C x y p)
  J C d x x (refl x) = d x

{-
  cong : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (x y : A)
       → x ＝ y
       → f x ＝ f y
  cong f = J (C f) (d f)
    where
    C : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → Π x ꞉ A , Π y ꞉ A , Π p ꞉ (Id _ x y) , 𝓥 ̇
    C {𝓤} {𝓥} {A} {B} f x y p = Id B (f x) (f y)
    d : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → Π x ꞉ A , C f x x (refl x)
    d f x = refl (f x)
-}

  subst : {A : 𝓤 ̇} (P : A → 𝓥 ̇) (x y : A)
        →  x ＝ y
        → P x → P y
  subst P = J (C P) (d P)
    where
    C : {A : 𝓤 ̇} (P : A → 𝓥 ̇) → Π x ꞉ A , Π y ꞉ A , Π p ꞉ (Id _ x y) , 𝓥 ̇
    C P x y p = P x → P y
    d : {A : 𝓤 ̇} (P : A → 𝓥 ̇) → Π x ꞉ A , C P x x (refl x)
    d P x = id


  lemma : {A : 𝓤 ̇} → Π x ꞉ A , Π y ꞉ A , Π p ꞉ (Id _ x y) , (Id _ (x , (refl x)) (y , p))
  lemma = J C d
    where
    C : {A : 𝓤 ̇} → Π x ꞉ A , Π y ꞉ A , Π p ꞉ (Id _ x y) , 𝓤 ̇
    C x y p = Id _ (x , (refl x)) (y , p)
    d : {A : 𝓤 ̇} → Π x ꞉ A , C x x (refl x)
    d x = refl (x , refl x)

  H : {A : 𝓤 ̇}
    → (x : A)
    → (D : (Π y ꞉ A , Π p ꞉ (Id _ x y) , 𝓥 ̇))
    → (d : (D x (refl x)))
    → (Π y ꞉ A , Π p ꞉ x ＝ y , D y p)
  H x D d x (refl x) = d

  H' : {A : 𝓤 ̇}
    → (x : A)
    → (D : (Π y ꞉ A , Π p ꞉ (Id _ x y) , 𝓥 ̇))
    → (d : (D x (refl x)))
    → (Π y ꞉ A , Π p ꞉ x ＝ y , D y p)
  H' x D d y p = subst (Σ-induction D) (x , refl x) (y , p) (lemma x y p) d 

  Hs-agreement : {A : 𝓤 ̇}
               → (x : A)
               → (D : (Π y ꞉ A , Π p ꞉ (Id _ x y) , 𝓥 ̇))
               → (d : (D x (refl x)))
               → (y : A)
               → (p : x ＝ y)
               → H x D d y p ＝ H x D d y p
  Hs-agreement x D d x (refl x) = refl d

--infix   0 _∼_
infixr 50 _,_
infixr 30 _×_
infixr 20 _+_
infixl 70 _∘_
infix   0 Id
infix   0 _＝_
--infix  10 _⇔_
--infixl 30 _∙_
--infixr  0 _＝⟨_⟩_
--infix   1 _∎
--infix  40 _⁻¹
--infix  10 _◁_
--infixr  0 _◁⟨_⟩_
--infix   1 _◀
--infix  10 _≃_
--infixl 30 _●_
--infixr  0 _≃⟨_⟩_
--infix   1 _■
--infix  40 _∈_
--infix  30 _[_,_]
infixr -1 -Σ
infixr -1 -Π
--infixr -1 -∃!
