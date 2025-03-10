{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C       : Set ℓ
  P Q         : A → Set ℓ
  x y z       : A
  f g h       : (x : A) → P x
  b b₁ b₂ b₃  : Bool
  k l m n     : Nat
  xs ys zs    : List A

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

transport : (P : A → Set ℓ) → x ≡ y → P x → P y
transport P refl p = p

zero+ : zero + n ≡ n
zero+ = refl

suc+ : (suc m) + n ≡ suc (m + n)
suc+ = refl

+zero : m + zero ≡ m
+zero {m = zero}  = refl
+zero {m = suc m} = cong suc +zero

+suc : m + (suc n) ≡ suc (m + n)
+suc {m = zero}  = refl
+suc {m = suc m} = cong suc +suc

{-# REWRITE +zero +suc #-}

+comm : m + n ≡ n + m
+comm {m = zero}  = refl
+comm {m = suc m} = cong suc (+comm {m = m})

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

infixr 5 _++_
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map-id : map (λ x → x) xs ≡ xs
map-id {xs = []}     = refl
map-id {xs = x ∷ xs} = cong (_∷_ x) map-id

map-fuse : map f (map g xs) ≡ map (λ x → f (g x)) xs
map-fuse {xs = []}     = refl
map-fuse {xs = x ∷ xs} = cong (_∷_ _) map-fuse

map-++ : map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
map-++ {xs = []}     = refl
map-++ {xs = x ∷ xs} = cong (_∷_ _) (map-++ {xs = xs})

{-# REWRITE map-id map-fuse map-++ #-}

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

swap : A × B → B × A
swap (x , y) = y , x

test₁ : map swap (map swap xs ++ map swap ys) ≡ xs ++ ys
test₁ = refl

-- Using map-++:
step₁ : map swap (map swap xs ++ map swap ys)
      ≡ map swap (map swap xs) ++ map swap (map swap ys)
step₁ = refl

-- Using map-fuse (likewise for ys)
step₂ : map swap (map swap xs)
      ≡ map (λ x → swap (swap x)) xs
step₂ = refl

-- Using eta-expansion
step₃ : map (λ x → swap (swap x)) xs
      ≡ map (λ x → swap (swap (fst x , snd x))) xs
step₃ = refl

-- Using definition of swap (2x)
step₄ : map (λ x → swap (swap (fst x , snd x))) xs
      ≡ map (λ x → (fst x , snd x)) xs
step₄ = refl

-- Using map-id (together with eta-contraction)
step₅ : map (λ x → (fst x , snd x)) xs ≡ xs
step₅ = refl

postulate
  Circle : Set
  base : Circle
  loop : base ≡ base

postulate
  Circle-elim : (P : Circle → Set ℓ)
    → (base* : P base)
    → (loop* : transport P loop base* ≡ base*)
    → (x : Circle) → P x
  elim-base : ∀ (P : Circle → Set ℓ) base* loop*
    → Circle-elim P base* loop* base ≡ base*
{-# REWRITE elim-base #-}

apd : (f : (x : A) → P x) (p : x ≡ y)
    → transport P p (f x) ≡ f y
apd f refl = refl

postulate
  elim-loop : ∀ (P : Circle → Set ℓ) base* loop*
    → apd (Circle-elim P base* loop*) loop ≡ loop*
{-# REWRITE elim-loop #-}

data _≐_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

postulate
  transportR : (P : A → Set ℓ) → x ≐ y → P x → P y
  transportR-refl : transportR P refl x ≡ x
{-# REWRITE transportR-refl #-}

variable
  R : A → A → Prop

postulate
  _//_    : (A : Set ℓ) (R : A → A → Prop) → Set ℓ
  proj    : A → A // R
  quot    : R x y → proj {R = R} x ≐ proj {R = R} y

  //-elim : (P : A // R → Set ℓ)
    → (proj* : (x : A) → P (proj x))
    → (quot* : {x y : A} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → (x : A // R) → P x
  //-beta : {R : A → A → Prop} (P : A // R → Set ℓ)
    → (proj* : (x : A) → P (proj x))
    → (quot* : {x y : A} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → {u : A} → //-elim P proj* quot* (proj u) ≡ proj* u
  -- Note: The type of //-beta mysteriously does not
  -- check when I leave out the {R : A → A → Prop},
  -- I'm not sure what's up with that.
{-# REWRITE //-beta #-}


record ⊤ {ℓ} : Prop ℓ where constructor tt

data   ⊥ {ℓ} : Prop ℓ where

record _∧_ (X : Prop ℓ₁) (Y : Prop ℓ₂) : Prop (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : X
    snd : Y
open _∧_

infix 6 _≅_
-- Observational equality
postulate
  _≅_ : {A : Set ℓ₁} {B : Set ℓ₂} → A → B → Prop (ℓ₁ ⊔ ℓ₂)

HEq = _≅_
syntax HEq {A = A} {B = B} x y = x ∈ A ≅ y ∈ B

postulate
  refl-Bool   : (Bool  ≅ Bool)  ≡ ⊤
  refl-true   : (true  ≅ true)  ≡ ⊤
  refl-false  : (false ≅ false) ≡ ⊤
  conflict-tf : (true  ≅ false) ≡ ⊥
  conflict-ft : (false ≅ true)  ≡ ⊥
{-# REWRITE refl-Bool refl-true refl-false
            conflict-tf conflict-ft #-}

postulate
  cong-Π : ((x : A) → P x) ≅ ((y : B) → Q y)
         ≡ (B ≅ A) ∧ ((x : A)(y : B) → y ≅ x → P x ≅ Q y)
  cong-λ : {A : Set ℓ₁} {B : Set ℓ₂}
    → {P : A → Set ℓ₃} {Q : B → Set ℓ₄}
    → (f : (x : A) → P x) (g : (y : B) → Q y)
    → ((λ x → f x) ≅ (λ y → g y))
    ≡ ((x : A) (y : B) (x≅y : x ≅ y) → f x ≅ g y)
{-# REWRITE cong-Π cong-λ #-}

infix 10 _[_⟩ _||_

postulate
  _[_⟩    : A → A ≅ B → B         -- Coercion
  _||_    : (x : A) (Q : A ≅ B)
          → x ∈ A ≅ x [ Q ⟩ ∈ B   -- Coherence

postulate
  coerce-Bool : b [ tt ⟩ ≡ b
{-# REWRITE coerce-Bool #-}

postulate
  coerce-Π : {A : Set ℓ₁} {B : Set ℓ₂}
    → {P : A → Set ℓ₃} {Q : B → Set ℓ₄}
    → {f : (x : A) → P x}
    → (ΠAP≅ΠBQ : ((x : A) → P x) ≅ ((y : B) → Q y))
    → _≡_ {A = (y : B) → Q y} (f [ ΠAP≅ΠBQ ⟩) λ (y : B) →
        let B≅A : B ≅ A
            B≅A = fst ΠAP≅ΠBQ
            x   : A
            x   = y [ B≅A ⟩
            Px≅Qy : P x ≅ Q y
            Px≅Qy = snd ΠAP≅ΠBQ x y (_||_ {B = A} y B≅A)
        in f x [ Px≅Qy ⟩
{-# REWRITE coerce-Π #-}
