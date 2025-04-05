
-- Some Agda encodings of lambda calculi interpreters drawing on
-- Adam Chlipala's
--
--  Parametric Higher-Order Abstract Syntax for Mechanized Semantics

module PHOAS where

data Bool : Set where
  false : Bool
  true  : Bool

infixr 30 _∧_
infixr 25 _∨_

_∧_ : Bool → Bool → Bool
false ∧ _ = false
true  ∧ b = b

_∨_ : Bool → Bool → Bool
false ∨ b = b
true  ∨ _ = true

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

module Untyped where
  infixr 40 _,_
  infixr 90 _•_

  data term (V : Set) : Set where
    var : V → term V
    u   : term V
    _,_ : term V → term V → term V
    fst : term V → term V
    snd : term V → term V
    lam : (V → term V) → term V
    _•_ : term V → term V → term V

  Term : Set1
  Term = ∀{V} → term V

  sub : ∀{V} → term (term V) → term V
  sub u       = u
  sub (var e) = e
  sub (a , b) = sub a , sub b
  sub (fst p) = fst (sub p)
  sub (snd p) = snd (sub p)
  sub (lam f) = lam (λ x → sub (f (var x)))
  sub (f • x) = sub f • sub x

  norm : forall {V} → term (term V) → term V
  norm u = u
  norm (var e) = e
  norm (a , b) = norm a , norm b
  norm (fst p) with norm p
  ...          | (a , _) = a
  ...          | e       = fst e
  norm (snd p) with norm p
  ...          | (_ , b) = b
  ...          | e       = fst e
  norm (lam f) = lam (λ x → norm (f (var x)))
  norm ((lam f) • x) = norm (f (norm x))
  norm (f • x) = norm f • norm x

  -- This is not a real normalize.
  normalize : Term → Term
  normalize t {V} = norm (t {term V})

  -- This 'normalizes' like...
  --
  --  The second half of the application normalizes to itself
  --  The first half of the application is applied to itself, yielding
  --    (var second-half) • (var second-half)
  --  The application is normalized, removing the 'var's, yielding
  --    second-half • second-half
  --  which is identical to the original.
  omega : Term
  omega = (lam (λ x → var x • var x)) • (lam (λ x → var x • var x))


module SimplyTyped where
  infixr 40 _×_
  infixr 20 _⇒_

  data Type : Set where
    unit : Type
    _×_  : Type → Type → Type
    _⇒_  : Type → Type → Type

  infixr 40 _,_
  infixl 90 _•_

  data term (V : Type → Set) : Type → Set where
    var   : {t : Type} → V t → term V t
    u     : term V unit
    _,_   : {t₁ t₂ : Type} → term V t₁ → term V t₂ → term V (t₁ × t₂)
    fst   : {t₁ t₂ : Type} → term V (t₁ × t₂) → term V t₁
    snd   : {t₁ t₂ : Type} → term V (t₁ × t₂) → term V t₂
    lam   : {t₁ t₂ : Type} → (V t₁ → term V t₂) → term V (t₁ ⇒ t₂)
    _•_   : {t₁ t₂ : Type} → term V (t₁ ⇒ t₂) → term V t₁ → term V t₂

  Term : Type → Set1
  Term t = ∀{V} → term V t

  sub : ∀{V t} → term (term V) t → term V t
  sub u       = u
  sub (var e) = e
  sub (a , b) = sub a , sub b
  sub (fst p) = fst (sub p)
  sub (snd p) = snd (sub p)
  sub (lam f) = lam (λ x → sub (f (var x)))
  sub (f • x) = sub f • sub x

  norm : forall {V t} → term (term V) t → term V t
  norm u       = u
  norm (var e) = e
  norm (a , b) = norm a , norm b
  norm (fst p) with norm p
  ...          | (a , _) = a
  ...          | t       = fst t
  norm (snd p) with norm p
  ...          | (_ , b) = b
  ...          | t       = snd t
  norm (lam f) = lam (λ x → norm (f (var x)))
  norm ((lam f) • x) = norm (f (norm x))
  norm (f • x) = norm f • norm x

  -- This is not a real normalize, either.
  normalize : ∀{t} → Term t → Term t
  normalize t {V} = norm {V} t


  N : Type → Set
  N _ = Nat

  infixr 35 _==_

  _==_ : Nat → Nat → Bool
  zero  == zero  = true
  suc m == suc n = m == n
  _     == _     = false


  id : ∀{t} → Term (t ⇒ t)
  id = lam (\x -> var x)

  first : ∀{t₁ t₂} → Term (t₁ × t₂ ⇒ t₁)
  first = lam (λ x → fst (var x))

  second : ∀{t₁ t₂} → Term (t₁ × t₂ ⇒ t₂)
  second = lam (λ x → snd (var x))

  dup : ∀{t} → Term (t ⇒ t × t)
  dup = lam (λ x → var x , var x)

  swap : ∀{t₁ t₂} → Term (t₁ × t₂ ⇒ t₂ × t₁)
  swap = lam (λ x → snd (var x) , fst (var x))

  test : Term unit
  test = (lam (λ x → id • var x)) • u

  test2 : Term unit
  test2 = (lam (λ x → id • id • var x)) • u
