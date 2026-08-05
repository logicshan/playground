
-- A short overview of what the categorical definitions of
-- final coalgebras and coinduction have to do with codata
-- in Agda. This is probably best read in combination with
-- a paper on the subject, like A Tutorial on (Co)algebras
-- and (Co)induction.
module Conat where

infixl 80 _∘_
_∘_ : ∀{A B C} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- The equality type
infix 40 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

≡-symm : ∀{A} {x y : A} → x ≡ y → y ≡ x
≡-symm refl = refl

≡-trans : ∀{A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

≡-ap : ∀{A B : Set} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
≡-ap refl _ = refl

-- The empty/false/initial type
data ⊥ : Set where

-- The singleton/true/final type
record ⊤ : Set where

-- sums
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- dependent sum, and a couple variations thereof that we won't use
infixr 50 _,_
data Σ (A : Set) (P : A → Set) : Set where
  _,_ : (x : A) (w : P x) → Σ A P

infixr 45 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

∃ : {A : Set} (P : A → Set) → Set
∃ {A} P = Σ A P

-- The only coinductive definition we'll use. Codata is still
-- having the kinks worked out of it in Agda (as far as practical
-- presentation of the underlying theory goes), and the current
-- recommended discipline is to make a single codata declaration
-- like the one below, and then encode νF as (something like):
--
--   data νF' : Set where in : F (∞ νF') → νF'
--   
--   νF : Set
--   νF = ∞ νF'
--
-- although one typically inlines F into the data definition,
-- and doesn't bother with the outermost ∞ (though I will here
-- because it's technically correct).
infix 30 ∞_
codata ∞_ (A : Set) : Set where
  ♯_ : A → ∞ A

-- observes come codata
♭ : ∀{A} → ∞ A → A
♭ (♯ x) = x

-- Extended naturals, adhering to the above discipline
data Conat : Set where
  cozero : Conat
  cosuc  : ∞ Conat → Conat

Coℕ : Set
Coℕ = ∞ Conat

-- some pseudo-constructors for Coℕ
zero : Coℕ
zero = ♯ cozero

suc : Coℕ → Coℕ
suc m = ♯ (cosuc m)

-- The coalgebra mophism guaranteed by the finality of Coℕ.
-- We can't use suc, because that doesn't satisfy the guardedness
-- criterion of the productivity checker.
unfold : ∀{A} → (A → ⊤ ⊎ A) → A → Coℕ
unfold step seed with step seed
... | inl _     = ♯ cozero
... | inr seed' = ♯ cosuc (unfold step seed')

{-
unfold : ∀{A} → (A → ⊤ ⊎ A) → A → Coℕ
unfold {A} step seed = ♯ aux (step seed)
 where
 aux : ⊤ ⊎ A → Conat
 aux (inl _)     = cozero
 aux (inr seed') = cosuc (unfold step seed')
-}

-- The relevant map for the Coℕ functor
map : ∀{A B} → (A → B) → ⊤ ⊎ A → ⊤ ⊎ B
map f (inl _) = inl _
map f (inr y) = inr (f y)

-- The coalgebra action for Coℕ
observe : Coℕ → ⊤ ⊎ Coℕ
observe cn with ♭ cn
... | cozero    = inl _
... | cosuc cn' = inr cn'

postulate
  -- Agda doesn't have extensional equality, so technically codata
  -- is only provably weakly final (existence but not uniqueness).
  -- Since that's no fun, I'll take the uniqueness part of finality
  -- as a postulate and use it to prove extensional equality for Coℕ.
  Coℕ! : ∀{A} → (step : A → ⊤ ⊎ A)        -- given a coalgebra
              → (g : A → Coℕ)              -- coalgebra morphisms to
              → observe ∘ g ≡ map g ∘ step --  the final coalgebra
              → g ≡ unfold step            --  are unique

  -- Extensional equality on functions also comes in handy. I don't
  -- think I can do without it here, but I may just be lazy.
  extensionality : ∀{A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

-- m ~ n is a bisimulation of m and n
infix 40 _~_
data _~_ : Conat → Conat → Set where
  cozero : cozero ~ cozero
  cosuc  : ∀{m n} → ∞ (♭ m ~ ♭ n) → cosuc m ~ cosuc n

-- Show that _~_ is an equivalence relation, for kicks.
~-refl : ∀ m → ♭ m ~ ♭ m
~-refl m with ♭ m
... | cozero   = cozero
... | cosuc m' = cosuc (♯ ~-refl m')

~-symm : ∀ m n → ♭ m ~ ♭ n → ♭ n ~ ♭ m
~-symm m n m~n with ♭ m | ♭ n
~-symm m n cozero      | cozero   | cozero   = cozero
~-symm m n ()          | cozero   | cosuc _
~-symm m n ()          | cosuc _  | cozero
~-symm m n (cosuc m~n) | cosuc m' | cosuc n' = cosuc (♯ ~-symm m' n' (♭ m~n))

~-trans : ∀ m n o → ♭ m ~ ♭ n → ♭ n ~ ♭ o → ♭ m ~ ♭ o
~-trans m n o m~n n~o with ♭ m | ♭ n | ♭ o
~-trans m n o m~n n~o                 | cozero   | cozero   | cozero   = cozero
~-trans m n o m~n ()                  | cozero   | cozero   | cosuc _
~-trans m n o () n~o                  | cozero   | cosuc n' | fo
~-trans m n o () n~o                  | cosuc m' | cozero   | fo
~-trans m n o m~n ()                  | cosuc m' | cosuc n' | cozero
~-trans m n o (cosuc m~n) (cosuc n~o) | cosuc m' | cosuc n' | cosuc o'
   = cosuc (♯ ~-trans m' n' o' (♭ m~n) (♭ n~o))

-- Bisim is the type of bisimulations on Coℕ. Showing
-- that this type is a ⊤ ⊎ ─ coalgebra is how we prove
-- extensional equality.
Bisim : Set
Bisim = Σ Coℕ λ m → Σ Coℕ λ n → ∞ (♭ m ~ ♭ n)

-- Here are two candidate coalgebra morphisms from Bisim to Coℕ
b-π₁ : Bisim → Coℕ
b-π₁ (m , _) = m

b-π₂ : Bisim → Coℕ
b-π₂ (_ , n , _) = n

-- This is a coalgebra action on Bisim
b-step : Bisim → ⊤ ⊎ Bisim
b-step (cm , cn , ext) with ♭ cm | ♭ cn | ♭ ext
... | .cozero    | .cozero    | cozero = inl _
... | .(cosuc m) | .(cosuc n) | cosuc {m} {n} ext' = inr (m , n , ext')

-- What do you know, b-π₁ and b-π₂ are, in fact, coalgebra
-- morphisms
eq₁ : observe ∘ b-π₁ ≡ map b-π₁ ∘ b-step
eq₁ = extensionality eq-aux
 where
 eq-aux : ∀ bi → observe (b-π₁ bi) ≡ map b-π₁ (b-step bi)
 eq-aux (cm , cn , ext) with ♭ cm | ♭ cn | ♭ ext
 ... | .cozero    | .cozero    | cozero             = refl
 ... | .(cosuc m) | .(cosuc n) | cosuc {m} {n} ext' = refl

eq₂ : observe ∘ b-π₂ ≡ map b-π₂ ∘ b-step
eq₂ = extensionality eq-aux
 where
 eq-aux : ∀ bi → observe (b-π₂ bi) ≡ map b-π₂ (b-step bi)
 eq-aux (cm , cn , ext) with ♭ cm | ♭ cn | ♭ ext
 ... | .cozero    | .cozero    | cozero             = refl
 ... | .(cosuc m) | .(cosuc n) | cosuc {m} {n} ext' = refl

-- Since they are, we can prove that they are equal (by
-- coinduction/finality), and thus applying them a single value
-- yields equal values. This allows us to prove the equality of
-- any two Coℕs for which we have a bisimulation. This is
-- extensional, as we have shown that two values are equal if
-- they produce the same sequence of observations.
bisim-≡ : ∀{m n} → ∞ (♭ m ~ ♭ n) → m ≡ n
bisim-≡ {m} {n} ext = ≡-ap lemma₃ (m , n , ext)
 where
 lemma₁ : b-π₁ ≡ unfold b-step
 lemma₁ = Coℕ! b-step b-π₁ eq₁

 lemma₂ : b-π₂ ≡ unfold b-step
 lemma₂ = Coℕ! b-step b-π₂ eq₂

 lemma₃ : b-π₁ ≡ b-π₂
 lemma₃ = ≡-trans lemma₁ (≡-symm lemma₂)

-- Extensional equality is pretty nice, because intensional
-- equality (the built-in kind in Agda, and all you'll normally
-- get out of _≡_ and such) doesn't even buy you the fact
-- that i and j below are equal (not that it should; you can
-- prove it in Coq (and could in the original codata implementation
-- Agda had), and that causes problems).
i : Coℕ
i = ♯ (cosuc i)

j : Coℕ
j = ♯ (cosuc i)

simple : i ≡ j
simple = bisim-≡ (♯ cosuc (♯ ~-refl i))

module Option1  where
  -- a defintion of addition that happens to admit an easy proof of
  -- commutativity.
  infixl 50 _+_
  _+_ : Coℕ → Coℕ → Coℕ
  m + n with ♭ m | ♭ n
  ... | cozero   | cozero   = ♯ cozero
  ... | cosuc m' | cozero   = ♯ cosuc m'
  ... | cozero   | cosuc n' = ♯ cosuc n'
  ... | cosuc m' | cosuc n' = ♯ cosuc (♯ cosuc (m' + n'))

  left-id : ∀ m → ♭ (zero + m) ~ ♭ m
  left-id m with ♭ m
  ... | cozero   = cozero
  ... | cosuc m' = cosuc (♯ ~-refl m')


  right-id : ∀ m → ♭ (m + zero) ~ ♭ m
  right-id m with ♭ m
  ... | cozero   = cozero
  ... | cosuc m' = cosuc (♯ ~-refl m')

  commute : ∀ m n → ♭ (m + n) ~ ♭ (n + m)
  commute m n with ♭ m | ♭ n
  ... | cozero   | cozero   = cozero
  ... | cozero   | cosuc n' = cosuc (♯ ~-refl n')
  ... | cosuc m' | cozero   = cosuc (♯ ~-refl m')
  ... | cosuc m' | cosuc n' = cosuc (♯ cosuc (♯ commute m' n'))

  ≡-commute : ∀ m n → m + n ≡ n + m
  ≡-commute m n = bisim-≡ {m + n} {n + m} (♯ commute m n)







