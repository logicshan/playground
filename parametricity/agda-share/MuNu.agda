{-# OPTIONS --type-in-type #-}

module MuNu where

record ⊤ : Set where

data Bool : Set where
  false : Bool
  true  : Bool

data Bit : Set where
  0# : Bit
  1# : Bit

infixr 50 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

id : ∀{A} → A → A
id x = x

codata ∞_ (A : Set) : Set where
  ♯_ : A → ∞ A

♭ : ∀{A} → ∞ A → A
♭ (♯ x) = x

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

bimap : ∀{A B C D} → (A → C) → (B → D) → A ⊎ B → C ⊎ D
bimap f _ (inl x) = inl (f x)
bimap _ g (inr y) = inr (g y)

mapl : ∀{A B C} → (A → B) → A ⊎ C → B ⊎ C
mapl f = bimap f id

mapr : ∀{A B C} → (B → C) → A ⊎ B → A ⊎ C
mapr g = bimap id g

data Σ (T : Set) (U : T → Set) : Set where
  _,_ : (x : T) (w : U x) → Σ T U

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

-- The type we're trying to encode is:
--    μ X. ν Y. Y + X 

module Direct where
  data Z (X : Set) : Set where
    [0] : ∞ Z X → Z X
    [1] :     X → Z X

  data O : Set where
    ↓ : Z O → O

  map-Z : ∀{A B} → (A → B) → Z A → Z B
  map-Z f ([0] z) = [0] (♯ map-Z f (♭ z))
  map-Z f ([1] x) = [1] (f x)

  -- this does not pass the termination/productivity check, and with
  -- good reason...
{-
  fold-O : ∀{R} → (Z R → R) → O → R
  fold-O {R} f = go
    where
    go : O → R
    go (↓ zo) = f (map-Z (fold-O f) zo)
-}

  -- ... because this does.
  01^ω : O
  01^ω = ↓ ([0] (♯ [1] 01^ω))

module Encode where
  -- these definitions generally need some sort of impredicativity,
  -- so we'll use type-in-type to simulate that.

  data ∃ (P : Set → Set) : Set where
    _,_ : ∀ T → P T → ∃ P

{-
  -- When Church encoding, abstract blocks make for much more readable
  -- types, but they block all computation, so we can't see the fruits
  -- of our labor.

  abstract
    μ : (Set → Set) → Set
    μ F = ∀ R → (F R → R) → R

    inμ : ∀{F} → (∀{T U} → (T → U) → F T → F U) → F (μ F) → μ F
    inμ map FμF R k = k (map (λ k' → k' R k) FμF)

    outμ : ∀{F} → (∀{T U} → (T → U) → F T → F U) → μ F → F (μ F)
    outμ {F} map μF = μF (F (μ F)) (map (inμ map))

    fold : ∀{F R} → (F R → R) → μ F → R
    fold {R = R} f μF = μF R f

  abstract
    ν : (Set → Set) → Set
    ν F = ∃ (λ S → S × (S → F S))

    unfold : ∀{F S} → S → (S → F S) → ν F
    unfold {F} {S} seed step = S , (seed , step)

    outν : ∀{F} → (∀{T U} → (T → U) → F T → F U) → ν F → F (ν F)
    outν map (T , (seed , step))
      = map (λ seed' → T , (seed' , step)) (step seed)

    inν : ∀{F} → (∀{T U} → (T → U) → F T → F U) → F (ν F) → ν F
    inν map FνF = unfold FνF (map (outν map))
-}

  μ : (Set → Set) → Set
  μ F = ∀ R → (F R → R) → R

  inμ : ∀{F} → (∀{T U} → (T → U) → F T → F U) → F (μ F) → μ F
  inμ map FμF R k = k (map (λ k' → k' R k) FμF)

  outμ : ∀{F} → (∀{T U} → (T → U) → F T → F U) → μ F → F (μ F)
  outμ {F} map μF = μF (F (μ F)) (map (inμ map))

  fold : ∀{F R} → (F R → R) → μ F → R
  fold {R = R} f μF = μF R f


  ν : (Set → Set) → Set
  ν F = ∃ (λ S → S × (S → F S))

  unfold : ∀{F S} → S → (S → F S) → ν F
  unfold {F} {S} seed step = S , (seed , step)

  outν : ∀{F} → (∀{T U} → (T → U) → F T → F U) → ν F → F (ν F)
  outν map (T , (seed , step))
      = map (λ seed' → T , (seed' , step)) (step seed)

  inν : ∀{F} → (∀{T U} → (T → U) → F T → F U) → F (ν F) → ν F
  inν map FνF = unfold FνF (map (outν map))

  Z : Set → Set
  Z T = ν (λ Y → Y ⊎ T)

  map-Z : ∀{T U} → (T → U) → Z T → Z U
  map-Z {T} {U} f z = unfold z step
   where
   step : Z T → Z T ⊎ U
   step seed = mapr f (outν mapl seed)

  O = μ Z

  ls : ∀{X} → Z X
  ls = unfold {S = ⊤} _ inl

  same : O
  same = inμ map-Z ls

  [1] : O → O
  [1] o = inμ map-Z (inν mapl (inr o))

  [0] : O → O
  [0] o = inμ map-Z (inν mapl (inl (outμ map-Z o)))

  test₁ : O
  test₁ = [0] ([1] ([0] ([1] ([1] same))))

-- We can convert from the μν fixed point to the νμ fixed point
convert : Encode.O → Direct.O
convert o = Encode.fold {Encode.Z} {Direct.O} (λ zo → Direct.↓ (pull zo)) o
 where
 pull : Encode.Z Direct.O → Direct.Z Direct.O
 pull zo with Encode.outν mapl zo
 pull zo | inl zo' = Direct.[0] (♯ pull zo')
 pull zo | inr o'  = Direct.[1] o'

-- These observe initial segments.
mutual
  tz : ℕ → Direct.Z Direct.O → List Bit
  tz zero    _        = []
  tz (suc n) (Direct.[0] zo) = 0# :: tz n (♭ zo)
  tz (suc n) (Direct.[1]  o) = 1# :: to n o

  to : ℕ → Direct.O → List Bit
  to n (Direct.↓ zo) = tz n zo

test₂ : Bit
test₂ = Encode.fold observe Encode.same
 where
 observe : Encode.Z Bit → Bit
 observe zb with Encode.outν mapl zb
 ... | inl _ = 0#
 ... | inr _ = 1#

-- 0# :: 1# :: 0# :: 1# :: 1# :: 0# :: 0# :: ...
test₃ : List Bit
test₃ = to 20 (convert Encode.test₁)

-- This fails the termination check, like Direct.fold-O above.
{-
convert' : Direct.O → Encode.O
convert' (Direct.↓ zo) = Encode.inμ Encode.map-Z (Encode.unfold zo pull)
 where
 pull : Direct.Z Direct.O → Direct.Z Direct.O ⊎ Encode.O
 pull (Direct.[0] l) = inl (♭ l)
 pull (Direct.[1] r) = inr (convert' r)

-- This is an Encode.O that contains infinite 1s
evil : Encode.O
evil = convert' Direct.01^ω

-- This is 10 copies of 0# 1#
test₄ : List Bit
test₄ = to 20 (convert evil)
-}

-- Given k and an o, this collects up-to-k length bit segments from
-- o and returns their catenation in a list. Essentially, o is of the
-- form:
--   <0s₁> 1 <0s₂> 1 <0s₃> 1 ...
-- where 0s_n is 0 or more 0s. pieces collects up the prefix of these
-- whose length is less than k (including the trailing 1), and puts
-- them all in a list. Importantly, since every legitimate element of
-- Encode.O ends with an infinite tail of 0s, this is guaranteed to
-- terminate, even though we don't have any preset limit on how many
-- segments to take, or anything of that sort, since the infinite
-- tail will exhaust any k (although some earlier large sequence of
-- 0s may exhaust various ks as well).
--
-- Thus, this is a demonstration that Encode.O is in fact
--    μ X. ν Y. Y + X
-- and does correctly only contain elements with infinite tails of 0s;
-- or, at least, evidence. Technically, a value of the form
--
--   101001000100001000001...
--
-- or similar would allow this function to terminate, so we've only shown
-- that every value of Encode.O must contain arbitrarily long strings of
-- 0s.
pieces : ℕ → Encode.O → List Bit
pieces n = Encode.fold (get n)
 where
 get : ℕ → Encode.Z (List Bit) → List Bit
 get zero    _   = []
 get (suc n) zlb with Encode.outν mapl zlb
 ... | inr lb   = 1# :: lb
 ... | inl zlb' = 0# :: get n zlb'

-- This hangs forever, since we've injected a spurious element from
-- Direct.O, which is νμ instead of μν
{-
test₅ : List Bit
test₅ = pieces 2 evil
-}