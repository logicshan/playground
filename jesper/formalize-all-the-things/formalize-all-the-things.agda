open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  A B C : Set
  x y z : A
  k l m n : Nat

it : ⦃ x : A ⦄ → A
it ⦃ x ⦄ = x

_ : Nat
_ = zero + 7 * (suc 3 - 1)

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing :     Maybe A

mapMaybe : (A → B) → (Maybe A → Maybe B)
mapMaybe f (just x) = just (f x)
mapMaybe f nothing = nothing

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

mapInl : (A → B) → A ⊎ C → B ⊎ C
mapInl f (inl x) = inl (f x)
mapInl f (inr y) = inr y

mapInr : (B → C) → A ⊎ B → A ⊎ C
mapInr f (inl x) = inl x
mapInr f (inr y) = inr (f y)

record ⊤ : Set where
  constructor tt     -- no fields

data ⊥ : Set where   -- no constructor

¬_ : Set → Set
¬ A = A → ⊥

-- “If A then B implies A”
ex₁ : A → (B → A)
ex₁ = λ z _ → z

-- “If A and true then A or false”
ex₂ : (A × ⊤) → (A ⊎ ⊥)
ex₂ = λ z → inl (fst z)

-- “If A implies B and B implies C then A implies C”
ex₃ : (A → B) → (B → C) → (A → C)
ex₃ = λ f g z → g (f z)

-- “It is not the case that not (either A or not A)”
ex₄ : ¬ (¬ (A ⊎ (¬ A)))
ex₄ = λ f → f (inr (λ x → f (inl x)))

_ : x ≡ x
_ = refl

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

module Nat-≤ where

  data _≤_ : Nat → Nat → Set where
    ≤-zero :         zero  ≤ n
    ≤-suc  : m ≤ n → suc m ≤ suc n

  ≤-refl : n ≤ n
  ≤-refl {n = zero}  = ≤-zero
  ≤-refl {n = suc k} = ≤-suc ≤-refl

  ≤-trans : k ≤ l → l ≤ m → k ≤ m
  ≤-trans ≤-zero      l≤m         = ≤-zero
  ≤-trans (≤-suc k≤l) (≤-suc l≤m) =
    ≤-suc (≤-trans k≤l l≤m)

  ≤-antisym : m ≤ n → n ≤ m → m ≡ n
  ≤-antisym ≤-zero      ≤-zero      = refl
  ≤-antisym (≤-suc m≤n) (≤-suc n≤m) =
    cong suc (≤-antisym m≤n n≤m)

  _ : 3 ≤ 5
  _ = ≤-suc (≤-suc (≤-suc ≤-zero))

  So : Bool → Set
  So false = ⊥
  So true  = ⊤

  instance
    ≤-dec : {p : So (m < suc n)} → m ≤ n
    ≤-dec {m = zero} {n = n} = ≤-zero
    ≤-dec {m = suc m} {n = suc n} {p = p} =
      ≤-suc (≤-dec {p = p})

  _ : 9000 ≤ 9001
  _ = it

record Ord (A : Set) : Set₁ where
  field
    _≤_       : A → A → Set
    ≤-refl    : x ≤ x
    ≤-trans   : x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : x ≤ y → y ≤ x → x ≡ y

  _≥_ : A → A → Set
  x ≥ y = y ≤ x

open Ord ⦃...⦄

instance
  Ord-Nat : Ord Nat
  _≤_       ⦃ Ord-Nat ⦄ = Nat-≤._≤_
  ≤-refl    ⦃ Ord-Nat ⦄ = Nat-≤.≤-refl
  ≤-trans   ⦃ Ord-Nat ⦄ = Nat-≤.≤-trans
  ≤-antisym ⦃ Ord-Nat ⦄ = Nat-≤.≤-antisym

instance
  Ord-⊤ : Ord ⊤
  _≤_       ⦃ Ord-⊤ ⦄ = λ _ _ → ⊤
  ≤-refl    ⦃ Ord-⊤ ⦄ = tt
  ≤-trans   ⦃ Ord-⊤ ⦄ = λ _ _ → tt
  ≤-antisym ⦃ Ord-⊤ ⦄ = λ _ _ → refl

module Example (A : Set) ⦃ A-≤ : Ord A ⦄ where

  example : {x y z : A} → x ≤ y → y ≤ z → z ≤ x → x ≡ y
  example x≤y y≤z z≤x = ≤-antisym {A = A} x≤y (≤-trans {A = A} y≤z z≤x)

data Tri ⦃ _ : Ord A ⦄ : A → A → Set where
  less    : ⦃ x≤y : x ≤ y ⦄ → Tri x y
  equal   : ⦃ x≡y : x ≡ y ⦄ → Tri x y
  greater : ⦃ x≥y : x ≥ y ⦄ → Tri x y

record TDO (A : Set) : Set₁ where
  field
    ⦃ Ord-A ⦄ : Ord A               -- superclass Ord
    tri       : (x y : A) → Tri x y

open TDO ⦃ ... ⦄ public

triNat : (x y : Nat) → Tri x y
triNat zero zero = equal
triNat zero (suc y) = less
triNat (suc x) zero = greater
triNat (suc x) (suc y) with triNat x y
... | less    ⦃ x≤y ⦄ = less    ⦃ x≤y = Nat-≤.≤-suc x≤y ⦄
... | equal   ⦃ x≡y ⦄ = equal   ⦃ x≡y = cong suc x≡y ⦄
... | greater ⦃ x≥y ⦄ = greater ⦃ x≥y = Nat-≤.≤-suc x≥y ⦄

instance
  TDO-Nat : TDO Nat
  Ord-A ⦃ TDO-Nat ⦄ = Ord-Nat
  tri   ⦃ TDO-Nat ⦄ = triNat

data [_]∞ (A : Set) : Set where
  -∞  :     [ A ]∞
  [_] : A → [ A ]∞
  +∞  :     [ A ]∞

variable
  lower upper : [ A ]∞

module Ord-[]∞ {A : Set} ⦃  A-≤ : Ord A ⦄ where

  data _≤∞_ : [ A ]∞ → [ A ]∞ → Set where
    -∞-≤ :          -∞   ≤∞   y
    []-≤ : x ≤ y → [ x ] ≤∞ [ y ]
    +∞-≤ :           x   ≤∞  +∞

  []∞-refl : x ≤∞ x
  []∞-refl { -∞}   = -∞-≤
  []∞-refl {[ x ]} = []-≤ (≤-refl {A = A})
  []∞-refl { +∞}   = +∞-≤

  []∞-trans : x ≤∞ y → y ≤∞ z → x ≤∞ z
  []∞-trans -∞-≤       _          = -∞-≤
  []∞-trans ([]-≤ x≤y) ([]-≤ y≤z) = []-≤ (≤-trans {A = A} x≤y y≤z)
  []∞-trans _          +∞-≤       = +∞-≤

  []∞-antisym : x ≤∞ y → y ≤∞ x → x ≡ y
  []∞-antisym -∞-≤       -∞-≤       = refl
  []∞-antisym ([]-≤ x≤y) ([]-≤ y≤x) = cong [_] (≤-antisym x≤y y≤x)
  []∞-antisym +∞-≤       +∞-≤       = refl

  instance
    Ord-[]∞ : ⦃ _ : Ord A ⦄ → Ord [ A ]∞
    _≤_       ⦃ Ord-[]∞ ⦄ = _≤∞_
    ≤-refl    ⦃ Ord-[]∞ ⦄ = []∞-refl
    ≤-trans   ⦃ Ord-[]∞ ⦄ = []∞-trans
    ≤-antisym ⦃ Ord-[]∞ ⦄ = []∞-antisym

open Ord-[]∞ public

module _ ⦃ _ : Ord A ⦄ where

  instance
    -∞-≤-I : {y : [ A ]∞} → -∞ ≤ y
    -∞-≤-I = -∞-≤

    +∞-≤-I : {x : [ A ]∞} → x ≤ +∞
    +∞-≤-I = +∞-≤

    []-≤-I : {x y : A} ⦃ x≤y : x ≤ y ⦄ → [ x ] ≤ [ y ]
    []-≤-I ⦃ x≤y = x≤y ⦄ = []-≤ x≤y


data BST (A : Set) ⦃ _ : Ord A ⦄
         (lower upper : [ A ]∞)  : Set where

  leaf : ⦃ l≤u : lower ≤ upper ⦄
       → BST A lower upper

  node : (x : A)
       → BST A lower [ x ]
       → BST A [ x ] upper
       → BST A lower upper

_ : BST Nat -∞ +∞
_ = node 42
      (node 6    leaf leaf)
      (node 9000 leaf leaf)

_ : BST Nat -∞ +∞
_ = node 42
      (node 6    (leaf ⦃ l≤u = -∞≤6 ⦄)    (leaf ⦃ l≤u = 6≤42 ⦄))
      (node 9000 (leaf ⦃ l≤u = 42≤9000 ⦄) (leaf ⦃ l≤u = 9000≤+∞ ⦄))

  where
    -∞≤6 : -∞ ≤ [ 6 ]
    -∞≤6 = it

    6≤42 : [ 6 ] ≤ [ 42 ]
    6≤42 = it

    42≤9000 : [ 42 ] ≤ [ 9000 ]
    42≤9000 = it

    9000≤+∞ : [ 9000 ] ≤ +∞
    9000≤+∞ = it

module Lookup ⦃ _ : TDO A ⦄ where

  data _∈_ {lower} {upper} (x : A) :
           (t : BST A lower upper) → Set where
    here  : ∀ {t₁ t₂} → x ≡ y  → x ∈ node y t₁ t₂
    left  : ∀ {t₁ t₂} → x ∈ t₁ → x ∈ node y t₁ t₂
    right : ∀ {t₁ t₂} → x ∈ t₂ → x ∈ node y t₁ t₂

  lookup : ∀ {lower} {upper}
         → (x : A) (t : BST A lower upper) → Maybe (x ∈ t)
  lookup x leaf = nothing
  lookup x (node y t₁ t₂) with tri x y
  ... | less    = mapMaybe left (lookup x t₁)
  ... | equal   = just (here it)
  ... | greater = mapMaybe right (lookup x t₂)

module Insert ⦃ _ : TDO A ⦄ where

  insert : (x : A) (t : BST A lower upper)
         → ⦃ l≤x : lower ≤ [ x ] ⦄ ⦃ x≤u : [ x ] ≤ upper ⦄
         → BST A lower upper
  insert x leaf = node x leaf leaf
  insert x (node y t₁ t₂) with tri x y
  ... | less    = node y (insert x t₁) t₂
  ... | equal   = node y t₁ t₂
  ... | greater = node y t₁ (insert x t₂)

  open Lookup

  insert-sound :
    (x : A) (t : BST A lower upper)
    → {{_ : lower ≤ [ x ]}} {{_ : [ x ] ≤ upper}}
    → (x ≡ y) ⊎ (y ∈ t) → y ∈ insert x t
  insert-sound x t (inl refl) = insert-sound₁ x t

    where

      insert-sound₁ :
        (x : A) (t : BST A lower upper)
        → {{_ : lower ≤ [ x ]}} {{_ : [ x ] ≤ upper}}
        → x ∈ insert x t
      insert-sound₁ x leaf = here refl
      insert-sound₁ x (node y t₁ t₂) with tri x y
      insert-sound₁ x (node y t₁ t₂) | less    = left (insert-sound₁ x t₁)
      insert-sound₁ x (node y t₁ t₂) | equal   = here it
      insert-sound₁ x (node y t₁ t₂) | greater = right (insert-sound₁ x t₂)

  insert-sound x t (inr y∈t) = insert-sound₂ x t y∈t

    where

      insert-sound₂ :
        (x : A) (t : BST A lower upper)
        → {{_ : lower ≤ [ x ]}} {{_ : [ x ] ≤ upper}}
        → y ∈ t → y ∈ insert x t
      insert-sound₂ x (node y t₁ t₂) (here  refl) with tri x y
      ... | less    = here refl
      ... | equal   = here refl
      ... | greater = here refl
      insert-sound₂ x (node y t₁ t₂) (left  y∈t₁) with tri x y
      ... | less    = left (insert-sound₂ x t₁ y∈t₁)
      ... | equal   = left y∈t₁
      ... | greater = left y∈t₁
      insert-sound₂ x (node y t₁ t₂) (right y∈t₂) with tri x y
      ... | less    = right y∈t₂
      ... | equal   = right y∈t₂
      ... | greater = right (insert-sound₂ x t₂ y∈t₂)

  insert-complete :
    (x : A) (t : BST A lower upper)
    → {{_ : lower ≤ [ x ]}} {{_ : [ x ] ≤ upper}}
    → y ∈ insert x t → (x ≡ y) ⊎ (y ∈ t)
  insert-complete x leaf           (here refl) = inl refl
  insert-complete x (node y t₁ t₂) y∈t'       with tri x y
  insert-complete x (node y t₁ t₂) (here refl)   | less    = inr (here refl)
  insert-complete x (node y t₁ t₂) (here refl)   | equal   = inl it
  insert-complete x (node y t₁ t₂) (here refl)   | greater = inr (here refl)
  insert-complete x (node y t₁ t₂) (left y∈t₁')  | less    = mapInr left (insert-complete x t₁ y∈t₁')
  insert-complete x (node y t₁ t₂) (left  y∈t₁)  | equal   = inr (left y∈t₁)
  insert-complete x (node y t₁ t₂) (left  y∈t₁)  | greater = inr (left y∈t₁)
  insert-complete x (node y t₁ t₂) (right y∈t₂)  | less    = inr (right y∈t₂)
  insert-complete x (node y t₁ t₂) (right y∈t₂)  | equal   = inr (right y∈t₂)
  insert-complete x (node y t₁ t₂) (right y∈t₂') | greater = mapInr right (insert-complete x t₂ y∈t₂')
