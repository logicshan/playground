
-- How to compute the inverse of an injective function

module Functional where

infixl 80 _∘_
_∘_ : ∀{a b c} → (b → c) → (a → b) → (a → c)
(g ∘ f) x = g (f x)

data Unit : Set where
  unit : Unit

data Nat : Set where
  z : Nat
  s : Nat → Nat
{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO    z   #-}
{-# BUILTIN SUC     s   #-}

data _≡_ {a : Set} (x : a) : a → Set where
  ≡-refl : x ≡ x

≡-trans : ∀{a} {x y z : a} → x ≡ y → y ≡ z → x ≡ z
≡-trans ≡-refl ≡-refl = ≡-refl

≡-symm : ∀{a} {x y : a} → x ≡ y → y ≡ x
≡-symm ≡-refl = ≡-refl

≡-resp : ∀{a b} {x y : a} (f : a → b) → x ≡ y → f x ≡ f y
≡-resp f ≡-refl = ≡-refl

-- a specialized (type-wise) version of the preorder
-- reasoning from the standard library.
module Reasoning {a : Set} where
  infix 40 _IsRelatedTo_
  infix 20 _∎
  infixr 20 _≈⟨_⟩_
  infix 10 begin_

  data _IsRelatedTo_ (x y : a) : Set where
    relTo : (x≡y : x ≡ y) → x IsRelatedTo y

  begin_ : ∀{x y} → x IsRelatedTo y → x ≡ y
  begin relTo x≡y = x≡y

  _≈⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x≡y ⟩ relTo y≡z = relTo (≡-trans x≡y y≡z)

  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo ≡-refl


data ∃ {a : Set} (P : a → Set) : Set where
  _,_ : (x : a) (w : P x) → ∃ P

data Σ (a : Set) (P : a → Set) : Set where
  _,_ : (x : a) (w : P x) → Σ a P

π₁ : ∀{a P} → Σ a P → a
π₁ (x , _) = x

π₂ : ∀{a P} → (p : Σ a P) → P (π₁ p)
π₂ (_ , w) = w

data Inspect {a : Set} (x : a) : Set where
  ins : (y : a) (y≡x : y ≡ x) → Inspect x

inspect : ∀{a} (x : a) → Inspect x
inspect x = ins x ≡-refl

injective : ∀{a b} → (a → b) → Set
injective f = ∀{x y} → f x ≡ f y → x ≡ y

surjective : ∀{a b} → (a → b) → Set
surjective f = ∀ y → ∃ (λ x → y ≡ f x)

data Image {a b : Set} (f : a → b) : Set where
  _⟶_⟨_⟩ : (x : a) (y : b) (eq : y ≡ f x) → Image f

π-img : ∀{a b} {f : a → b} → Image f → b
π-img (_ ⟶ y ⟨ _ ⟩) = y

id : ∀{a : Set} → a → a
id x = x

id-inj : ∀{a} → injective (id {a})
id-inj = id -- yow!

-- agrees f f' stipulates that f' maps elements of its
-- domain to the same values as f, modulo being wrapped
-- by Image stuff.
agrees : ∀{a b} (f : a → b) (f' : a → Image f) → Set
agrees f f' = ∀ x → f x ≡ π-img (f' x)

-- This proves that if a function f is injective, then for any
-- function f' that behaves as f restricted to its image, there
-- is a left-inverse of f'. The proof is stated in this manner
-- so that it has to work even if f' behaves similarly to a
-- proper restriction of f to its image, which would likely
-- require quotient types; see restrict below.
--
-- An example would be, for some f : a → b, define equivalence
-- classes [x] for x ∈ a, using a relation x ~ y ⟷ f x ≡ f y.
-- Then, suppose we have a function g : a/~ → a such that [g y] = y.
-- We can define
--
--    canonize : a → a
--    canonize x = g [x]
--
-- And then define
--
--    f' : a → Image f
--    f' x = canonize x ⟶ f x ⟨ whatever ⟩
--
-- So, an element of Image f gives us no information about which
-- value was used to construct it, only what the corresponding
-- canonical value is. But, f' agrees on f, so our proof must
-- still work for this f'.
inj-inv : ∀{a b} {f : a → b} → injective f → (f' : a → Image f) → agrees f f'
        → ∃ {Image f → a} (λ g → ∀ x → x ≡ g (f' x))
inj-inv {a} {b} {f} inj-f f' agree = (g , pf)
 where
 g : Image f → a
 g (x ⟶ _ ⟨ _ ⟩) = x
 pf : ∀ x → x ≡ g (f' x)
 pf x with f' x                 | agree x
 ...  | x' ⟶ .(f x) ⟨ fx≡fx' ⟩ | ≡-refl = inj-f fx≡fx'


-- test
const-0 : ∀{a} → a → Nat
const-0 _ = 0

restricted-0 : ∀{a} → a → a → Image (const-0 {a})
restricted-0 x _ = x ⟶ 0 ⟨ ≡-refl ⟩

agree-0 : ∀{a x} → agrees (const-0 {a}) (restricted-0 {a} x)
agree-0 _ = ≡-refl

≡-refl-unit : ∀{x y : Unit} → x ≡ y
≡-refl-unit {unit} {unit} = ≡-refl

injective-0 : injective (const-0 {Unit})
injective-0 0≡0 = ≡-refl-unit

inverse-0 : ∃ (λ g → ∀ x → x ≡ g (restricted-0 unit x))
inverse-0 = inj-inv injective-0 (restricted-0 unit) (agree-0 {_} {unit})

inj-∘ : ∀{a b c} {f : a → b} {g : b → c} → injective f → injective g
      → injective (g ∘ f)
inj-∘ inj-f inj-g = inj-f ∘ inj-g

-- This produces a version of a function whose codomain is precisely
-- its image...
restrict : ∀{a b} (f : a → b) → a → Image f
restrict f x = x ⟶ f x ⟨ ≡-refl ⟩

-- However, Image f is actually too large a type, because it stores
-- the element of a that was used to produce the given element of b.
-- Thus, restrict f x₁ ≢ restrict f x₂ even if f x₁ ≡ f x₂. A true
-- Image type would be a quotient of the one we're able to build in
-- Agda.
restrict-inv : ∀{a b} {f : a → b} 
             → ∃ {Image f → a} (λ g → ∀ x → g (restrict f x) ≡ x)
restrict-inv {a} {b} {f} = (g , λ x → ≡-refl)
 where
 g : Image f → a
 g (x ⟶ _ ⟨ _ ⟩) = x

-- We can prove restrict f is injective regardless of f.
restrict-inj : ∀{a b} {f : a → b} → injective (restrict f)
restrict-inj ≡-refl = ≡-refl

-- An alternate way of setting up all the machinery
data _∈img_ {a b : Set} : b → (a → b) → Set where
  point : {f : a → b} (x : a) → f x ∈img f

image : ∀{a b} → (a → b) → Set
image {b = b} f = Σ b (λ y → y ∈img f)

agrees' : ∀{a b} (f : a → b) (f' : a → image f) → Set
agrees' f f' = ∀ x → f x ≡ π₁ (f' x)

by-definition : ∀{a} {x : a} → x ≡ x
by-definition = ≡-refl

inj-inf' : ∀{a b} {f : a → b} → injective f → (f' : a → image f) → agrees' f f'
         → ∃ {image f → a} (λ g → ∀ x →  x ≡ g (f' x))
inj-inf' {a} {b} {f} inj-f f' agree = (g , pf)
 where
 g : image f → a
 g (.(f x) , point x) = x
 pf : ∀ x → x ≡ g (f' x)
 pf x with inspect (f' x) | agree x             
 ...  | ins (.(f x') , point x') eq | fx≡fx' = begin
                                                 x
                                               ≈⟨ inj-f lem₂ ⟩
                                                 x'
                                               ≈⟨ ≡-symm lem₁ ⟩
                                                 g (f' x)
                                               ∎
  where
  open Reasoning
  lem₁ : g (f' x) ≡ x'
  lem₁ = begin
           g (f' x)
         ≈⟨ ≡-resp g (≡-symm eq) ⟩
           g (f x' , point x')
         ≈⟨ by-definition ⟩
           x'
         ∎
  lem₂ : f x ≡ f x'
  lem₂ = begin
           f x
         ≈⟨ fx≡fx' ⟩
           π₁ (f' x)
         ≈⟨ ≡-resp π₁ (≡-symm eq) ⟩
           -- skip a by-definition to avoid filling in metas
           f x'
         ∎

