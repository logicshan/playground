{-# OPTIONS --type-in-type --no-positivity-check #-}

-- Some delimited continuation monads represented syntactically

module DC where

open import Data.Nat
open import Data.List
open import Data.Unit

record Functor (F : Set → Set) : Set where
  infixl 40 _⟨$⟩_
  field
    _⟨$⟩_ : ∀{A B} → (A → B) → F A → F B

  _⟨$_ : ∀{A B} → A → F B → F A
  x ⟨$ m = (λ _ → x) ⟨$⟩ m

record Idiom (F : Set → Set) : Set where
  infixl 40 _⟨∗⟩_
  field
    pure  : ∀{A}   → A → F A
    _⟨∗⟩_ : ∀{A B} → F (A → B) → F A → F B

    func  : Functor F

  open Functor func public

  lift₂ : ∀{A B C} → (A → B → C) → F A → F B → F C
  lift₂ f x y = f ⟨$⟩ x ⟨∗⟩ y

  _⟨_⟩_ : ∀{A B C} → F A → (A → B → C) → F B → F C
  x ⟨ f ⟩ y = lift₂ f x y

  _⟨∗_ : ∀{A B} → F A → F B → F A
  _⟨∗_ = lift₂ (λ x _ → x)

  _∗⟩_ : ∀{A B} → F A → F B → F B
  _∗⟩_ = lift₂ (λ _ y → y)

  for_ : ∀{A B} → List A → (A → F B) → F ⊤
  for_ []       _ = pure _
  for_ (x ∷ xs) f = f x ∗⟩ for_ xs f

  for : ∀{A B} → List A → (A → F B) → F (List B)
  for []       _ = pure []
  for (x ∷ xs) f = _∷_ ⟨$⟩ f x ⟨∗⟩ for xs f

record Monad (F : Set → Set) : Set where
  field
    _>>=_ : ∀{A B} → F A → (A → F B) → F B

    idiom : Idiom F

  open Idiom idiom public

  _>>_ : ∀{A B} → F A → F B → F B
  m >> n = m >>= λ _ → n

  infixr 30 _=<<_
  _=<<_ : ∀{A B} → (A → F B) → F A → F B
  f =<< m = m >>= f

module MkMonad (F : Set → Set)
               (η : ∀{A} → A → F A)
               (extend : ∀{A B} → (A → F B) → F A → F B) where

  FF : Functor F
  FF = record { _⟨$⟩_ = λ f → extend (λ x → η (f x))
              }

  FI : Idiom F
  FI = record { pure  = η
              ; _⟨∗⟩_ = λ f m → extend (λ g → extend (λ x → η (g x)) m) f
              ; func  = FF
              }

  FM : Monad F
  FM = record { _>>=_ = λ m f → extend f m
              ; idiom = FI
              }

-- shift/reset
module SR where
  data Cont (R A : Set) : Set where
    pur  : A → Cont R A
    shft : ∀{B} → ((B → R) → R) → (B → Cont R A) → Cont R A

  extend : ∀{A B R} → (A → Cont R B) → Cont R A → Cont R B
  extend f (pur x)    = f x
  extend f (shft g h) = shft g (λ x → extend f (h x))

  open module M {R} = MkMonad (Cont R) pur extend

  shift : ∀{A R} → ((A → R) → R) → Cont R A
  shift f = shft f pur

  -- Resetting yields a pure value. No control effects can escape.
  reset : ∀{R} → Cont R R → R
  reset (pur x)    = x
  reset (shft f k) = f (λ x → reset (k x))

  open Monad FM

  test₁ : ℕ
  test₁ = reset (shift (λ k → k (k (k 5))) ⟨ _+_ ⟩ pure 1)
  -- 8

  test₂ : ℕ
  test₂ = reset (shift (λ k → k 5 + 1) ⟨ _+_ ⟩ shift (λ _ → 0))
  -- 1

-- control/prompt
module CP where
  -- This is where the negativity comes in.
  -- For carrier C, the control operation seems to have signature:
  -- R^(C^B) × C^B → C
  data Cont (R A : Set) : Set where
    pur  : A → Cont R A
    ctrl : ∀{B} → ((B → Cont R R) → R) → (B → Cont R A) → Cont R A

  extend : ∀{A B R} → (A → Cont R B) → Cont R A → Cont R B
  extend f (pur x)    = f x
  extend f (ctrl g h) = ctrl g (λ x → extend f (h x))

  open module M {R} = MkMonad (Cont R) pur extend

  control : ∀{A R} → ((A → Cont R R) → R) → Cont R A
  control f = ctrl f pur

  prompt : ∀{R} → Cont R R → R
  prompt (pur x)    = x
  prompt (ctrl f k) = f k

  open Monad FM

  test₁ : ℕ                    -- v-- not ideal
  test₁ = prompt (control (λ k → prompt (k =<< k =<< k 5)) ⟨ _+_ ⟩ pure 1)
  -- 8

  test₂ : ℕ
  test₂ = prompt (control (λ k → prompt (k 5 ⟨ _+_ ⟩ pure 1)) 
                    ⟨ _+_ ⟩
                  control (λ _ → 0))
  -- 0
