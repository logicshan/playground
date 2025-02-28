{-# OPTIONS --allow-unsolved-metas #-}
{-
  AGDA IN PADOVA 2024
  Exercise sheet 5

  ┌─ SHORTCUTS ───────────────────────┐    ┌─ BACKSLASH CHARACTERS ─┐
  │ C-c C-l   = load file             │    │ \bN    = ℕ             │
  │ C-c C-c   = case split            │    │ \alpha = α             │
  │ C-c C-SPC = check hole            │    │ \to    = →             │
  │ C-c C-,   = see context           │    │ \cdot  = ·             │
  │ C-c C-.   = see context and goal  │    │ \::    = ∷             │
  │ C-c C-d   = display type          │    │ \==    = ≡             │
  │ C-c C-v   = evaluate expression   │    └────────────────────────┘
  │ C-z       = enable Vi keybindings │    Use M-x describe-char to
  │ C-x C-+   = increase font size    │    lookup input method for
  └───────────────────────────────────┘    symbol under cursor.

  You can open this file in an Agdapad session by pressing C-x C-f ("find file")
  and then entering the path to this file: ~/Padova2024/exercise05.agda.
  As this file is read-only, you can then save a copy of this file to your personal
  directory and edit that one: File > Save As... For instance, you can save this file
  as ~/solutions05.agda.
-}

open import Padova2024.EquationalReasoning
{-# BUILTIN EQUALITY _≡_ #-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data ⊥ : Set where

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)


-- ──────────────────────────────────────────────────────
-- ────[ PROPERTIES OF THE ORDERING OF THE NATURALS ]────
-- ──────────────────────────────────────────────────────

data _<_ : ℕ → ℕ → Set where
  base : {n : ℕ}   → n < succ n
  step : {a b : ℕ} → a < b      → a < succ b

zero< : {x : ℕ} → zero < succ x
zero< {zero} = base
zero< {succ x} = step zero<

succ<succ : {x y : ℕ} → x < y → succ x < succ y
succ<succ {zero} {zero} ()
succ<succ {zero} {succ .zero} base = base
succ<succ {zero} {succ y} (step p) = step (succ<succ p)
succ<succ {succ x} {zero} ()
succ<succ {succ x} {succ .(succ x)} base = base
succ<succ {succ x} {succ y} (step p) = step (succ<succ p)

-- EXERCISE: Verify that the successor operation is monotonic.
lemma-succ-monotonic : {a b : ℕ} → a < b → succ a < succ b
lemma-succ-monotonic base = base
lemma-succ-monotonic (step p) = step (lemma-succ-monotonic p)

-- EXERCISE: Verify that half of a number is (almost) always smaller than the number.
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

_×_ : ℕ → ℕ → ℕ
zero × n = zero
succ m × n = n + (m × n)

_^_ : ℕ → ℕ → ℕ
zero ^ zero = succ zero
zero ^ _ = zero
_ ^ zero = succ zero
m ^ succ n = m × (m ^ n)

+zero : {x : ℕ} → (x + zero) ≡ x
+zero {zero} = refl
+zero {succ x} = cong succ +zero

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

+comm : {x y : ℕ} → (x + y) ≡ (y + x)
+comm {zero} {zero} = refl
+comm {zero} {succ y} = cong succ (symm (+zero {y})) 
+comm {succ x} {zero} = cong succ (+zero {x})
+comm {succ x} {succ y} rewrite lemma-+-succ x y | lemma-+-succ y x
  = cong (λ z → succ (succ z)) (+comm {x} {y})

+ass : {x y z : ℕ} → (x + (y + z)) ≡ ((x + y) + z)
+ass {zero} {zero} {zero} = refl
+ass {zero} {zero} {succ z} = refl
+ass {zero} {succ y} {zero} = refl
+ass {zero} {succ y} {succ z} = refl
+ass {succ x} {zero} {zero} rewrite +zero {x} | +zero {x} = refl
+ass {succ x} {zero} {succ z} rewrite +zero {x} = refl
+ass {succ x} {succ y} {zero} rewrite +zero {y} | +zero {x + succ y} = refl
+ass {succ x} {succ y} {succ z} rewrite lemma-+-succ x (y + succ z)
                                      | lemma-+-succ x y
                                      | lemma-+-succ y z
                                      | lemma-+-succ x (y + z)
                                      | lemma-+-succ (x + y) z = cong (λ v → succ (succ (succ v))) (+ass {x} {y} {z})

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

n-step : {x : ℕ} → (n : ℕ) → x < succ (n + x)
n-step zero = base
n-step (succ n) = step (n-step n)

data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

-- "Odd n" is the type of witnesses that "n" is odd.
data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

even→odd : {n : ℕ} → Even n → Odd (succ n)
even→odd base-even = base-odd
even→odd (step-even p) = step-odd (even→odd p)

odd→even : {n : ℕ} → Odd n → Even (succ n)
odd→even base-odd = step-even base-even
odd→even (step-odd p) = step-even (odd→even p)

parity : (n : ℕ) → Even n ⊎ Odd n
parity zero = left base-even
parity (succ n) with parity n
... | left en = right (even→odd en)
... | right on = left (odd→even on)

half-even : {n : ℕ} → Even n → (half (succ n) + half (succ n)) ≡ n
half-even base-even = refl
half-even (step-even {n} p)
  rewrite lemma-+-succ (half (succ n)) (half (succ n))= cong (λ x → succ (succ x)) (half-even p)

half-odd : {n : ℕ} → Odd n → (half n + half (succ n)) ≡ n
half-odd base-odd = refl
half-odd (step-odd {n} p) = begin
  succ (half n + succ (half (succ n)))
    ≡⟨ cong succ (lemma-+-succ (half n) (half (succ n))) ⟩
  succ (succ ((half n) + (half (succ n))))
    ≡⟨ cong (λ x → succ (succ x)) (half-odd {n} p) ⟩
  succ (succ n) ∎

lemma-half< : (a : ℕ) → half (succ a) < succ a
lemma-half< a with parity a
... | left ea = lemmaₑ (n-step {half (succ a)} (half (succ a)))
  where 
    lemmaₑ : half (succ a) < succ (half (succ a) + half (succ a)) → half (succ a) < succ a
    lemmaₑ rewrite half-even ea = λ z → z
... | right oa = lemmaₒ (n-step {half (succ a)} (half a))
  where
    lemmaₒ : (half (succ a) < succ (half a + half (succ a))) → half (succ a) < succ a
    lemmaₒ rewrite half-odd oa = λ z → z


-- EXERCISE: Verify that the following alternative definition of the less-than relation is equivalent to _<_.
data _<'_ : ℕ → ℕ → Set where
  base : {n : ℕ}   → zero <' succ n
  step : {a b : ℕ} → a <' b → succ a <' succ b

trans<' : {a b c : ℕ} → a <' b → b <' c → a <' c
trans<' base (step q) = base
trans<' (step p) (step q) = step (trans<' p q)

<'succ : {x : ℕ} → x <' succ x
<'succ {zero} = base
<'succ {succ x} = step <'succ

<→<' : {a b : ℕ} → a < b → a <' b
<→<' {zero} {zero} ()
<→<' {zero} {succ .zero} base = base
<→<' {zero} {succ b} (step p) = base
<→<' {succ a} {zero} ()
<→<' {succ a} {succ .(succ a)} base = step (<→<' base)
<→<' {succ a} {succ b} (step p) = trans<' (<→<' {succ a} {b} p) <'succ

<'→< : {a b : ℕ} → a <' b → a < b
<'→< {zero} {zero} ()
<'→< {zero} {succ b} base = zero<
<'→< {succ a} {zero} ()
<'→< {succ a} {succ b} (step p) = succ<succ (<'→< p)


-- ────────────────────────────────────────────────────────
-- ────[ INTERLUDE: BINARY REPRESENTATIONS OF NUMBERS ]────
-- ────────────────────────────────────────────────────────

data Bin : Set where
  [] : Bin
  _O : Bin → Bin
  _I : Bin → Bin
-- For instance: The number 6 (binary 110) is encoded as [] I I O.
-- This is a shorthand for _O (_I (_I [])).

double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

-- EXERCISE: Implement the successor operation on binary representations.
-- For instance, succ' ([] I I O) should be [] I I I.
succ' : Bin → Bin
succ' [] = [] I
succ' (b O) = b I
succ' (b I) = (succ' b) O

-- EXERCISE: Implement the following function. It should be left inverse to the
-- "encode" function below.
decode : Bin → ℕ
decode [] = zero
decode (b O) = decode b + decode b
decode (b I) = succ (decode b + decode b)

encode : ℕ → Bin
encode zero     = []
encode (succ n) = succ' (encode n)

-- EXERCISE: Show that "succ'" is on binary representations what "succ" is on natural numbers.
-- Hint: You will need to use the "cong" function.
lemma-succ-succ' : (xs : Bin) → decode (succ' xs) ≡ succ (decode xs)
lemma-succ-succ' [] = refl
lemma-succ-succ' (xs O) = refl
lemma-succ-succ' (xs I)
  rewrite lemma-succ-succ' xs | lemma-+-succ (decode xs) (decode xs) = refl

-- EXERCISE: Show that "decode" and "encode" are [one-sided] inverses of each other.
lemma-decode-encode : (n : ℕ) → decode (encode n) ≡ n
lemma-decode-encode zero = refl
lemma-decode-encode (succ n)
  rewrite lemma-succ-succ' (encode n) = cong succ (lemma-decode-encode n)

-- EXERCISE: Implement binary addition and verify that it works correctly by comparing
-- to the standard addition on natural numbers.
_+'_ : Bin → Bin → Bin
[] +' y = y
x +' [] = x
(x O) +' (y O) = (x +' y) O
(x O) +' (y I) = (x +' y) I
(x I) +' (y O) = (x +' y) I
(x I) +' (y I) = (succ' (x +' y)) O

+'[] : {b : Bin} → (b +' []) ≡ b
+'[] {[]} = refl
+'[] {b O} = refl
+'[] {b I} = refl

+'succ : {x y : Bin} → (x +' (succ' y)) ≡ succ' (x +' y)
+'succ {[]} {[]} = refl
+'succ {[]} {y O} = refl
+'succ {[]} {y I} = refl
+'succ {x O} {[]} rewrite +'[] {x} = refl
+'succ {x O} {y O} = refl
+'succ {x O} {y I} rewrite +'succ {x} {y} = refl
+'succ {x I} {[]} rewrite +'[] {x} = refl
+'succ {x I} {y O} = refl
+'succ {x I} {y I} rewrite +'succ {x} {y} = refl

succ'+' : {x y : Bin} → (succ' x +' y) ≡ (succ' (x +' y))
succ'+' {[]} {[]} = refl
succ'+' {[]} {y O} = refl
succ'+' {[]} {y I} = refl
succ'+' {x O} {[]} = refl
succ'+' {x O} {y O} = refl
succ'+' {x O} {y I} = refl
succ'+' {x I} {[]} = refl
succ'+' {x I} {y O} rewrite succ'+' {x} {y} = refl
succ'+' {x I} {y I} rewrite succ'+' {x} {y} = refl


helper : {a b : Bin} → ((decode a + decode b) + (decode a + decode b)) ≡ ((decode a + decode a) + (decode b + decode b))
helper {a} {b} rewrite +ass {decode a + decode b} {decode a} {decode b}
                     | symm (+ass {decode a} {decode b} {decode a})
                     | +comm {decode b} {decode a}
                     | +ass {decode a} {decode a} {decode b}
                     | symm (+ass {decode a + decode a} {decode b} {decode b})
                     = refl

lemma-+-+'₂ : (x y : ℕ) → encode (x + y) ≡ (encode x +' encode y)
lemma-+-+'₂ zero zero = refl
lemma-+-+'₂ zero (succ y) = refl
lemma-+-+'₂ (succ x) zero rewrite +zero {x} | +'[] {succ' (encode x)} = refl
lemma-+-+'₂ (succ x) (succ y) rewrite +'succ {succ' (encode x)} {encode y}
                                    | lemma-+-succ x y
                                    | lemma-+-+'₂ x y
                                    | succ'+' {encode x} {encode y}
                                    = refl

lemma-+-+' : (x y : Bin) → decode (x +' y) ≡ (decode x + decode y)
lemma-+-+' [] [] = refl
lemma-+-+' [] (y O) = refl
lemma-+-+' [] (y I) = refl
lemma-+-+' (x O) [] rewrite +zero {decode x + decode x} = refl
lemma-+-+' (x O) (y O) rewrite lemma-+-+' x y = helper {x} {y}
lemma-+-+' (x O) (y I) rewrite lemma-+-+' x y
                             | lemma-+-succ (decode x + decode x) (decode y + decode y)
                             = cong succ (helper {x} {y})
lemma-+-+' (x I) [] rewrite +zero {decode x + decode x} = refl
lemma-+-+' (x I) (y O) rewrite lemma-+-+' x y
                             | lemma-+-succ (decode x + decode x) (decode y + decode y)
                             = cong succ (helper {x} {y})
lemma-+-+' (x I) (y I) rewrite lemma-succ-succ' (x +' y)
                             | lemma-+-succ (decode (x +' y)) (decode (x +' y))
                             | lemma-+-+' x y
                             | lemma-+-succ (decode x + decode x) (decode y + decode y)
                             = cong (λ z → succ (succ z)) (helper {x} {y})

-- ────────────────────────────────────────
-- ────[ USING NATURAL NUMBERS AS GAS ]────
-- ────────────────────────────────────────
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n          -- 0 ≤ 任意自然数 n
  s≤s : ∀ {m n} → m ≤ n → succ m ≤ succ n  -- 若 m ≤ n，则 succ m ≤ succ n

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {succ n} = s≤s ≤-refl

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n _ = z≤n
≤-trans (s≤s a≤b) (s≤s b≤c) = s≤s (≤-trans a≤b b≤c)

≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s a≤b) (s≤s b≤a) = cong succ (≤-antisym a≤b b≤a)

≤-step : ∀ {m n} → m ≤ n → m ≤ succ n
≤-step z≤n       = z≤n        -- 0 ≤ n 直接推导出 0 ≤ succ n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)  -- 递归应用

<→≤'' : {m n : ℕ} → m < n → m ≤ n
<→≤'' {m} {n} p with <→<' p
... | base = z≤n
... | step q = s≤s (<→≤'' (<'→< q))

<→≤ : {m n : ℕ} → m < (succ n) → m ≤ n
<→≤ {zero} {zero} base = z≤n
<→≤ {zero} {succ n} (step p) = z≤n
<→≤ {succ m} {succ .m} base = s≤s (<→≤ base)
<→≤ {succ m} {succ n} (step p) = <→≤'' p 

lemma-≤'''' : {n : ℕ} → half (succ n) ≤ succ (half n)
lemma-≤''' : {n : ℕ} → half n ≤ half (succ n)

lemma-≤'''' {zero} = z≤n
lemma-≤'''' {succ n} = s≤s (lemma-≤''' {n})

lemma-≤''' {zero} = z≤n
lemma-≤''' {succ n} = lemma-≤'''' {n}

lemma-≤'' : {n m : ℕ} → n ≤ m → half (succ n) ≤ succ m
lemma-≤'' {zero} {zero} z≤n = z≤n
lemma-≤'' {zero} {succ m} z≤n = z≤n
lemma-≤'' {succ n} {zero} ()
lemma-≤'' {succ n} {succ m} (s≤s p) = s≤s (≤-trans (lemma-≤''' {n}) (lemma-≤'' {n} {m} p))

lemma-≤' : {n m : ℕ} → n ≤ m → half n ≤ m
lemma-≤' {zero} {zero} z≤n = z≤n
lemma-≤' {zero} {succ m} z≤n = z≤n
lemma-≤' {succ n} {zero} ()
lemma-≤' {succ n} {succ m} (s≤s p) = lemma-≤'' {n} {m} p

lemma-≤ : {n m : ℕ} → n ≤ m → half (succ n) ≤ m
lemma-≤ {zero} {zero} z≤n = z≤n
lemma-≤ {zero} {succ m} z≤n = z≤n
lemma-≤ {succ n} {zero} ()
lemma-≤ {succ n} {succ m} (s≤s p) = s≤s (lemma-≤' {n} {m} p)

module NaiveGas where
  go : ℕ → ℕ → ℕ
  go zero     gas        = zero
  go (succ n) zero       = zero   -- bailout case
  go (succ n) (succ gas) = succ (go (half (succ n)) gas)

  digits : ℕ → ℕ
  digits n = go n n

  lemma-half-succ : (x : ℕ) → half (succ x) ≤ x
  lemma-half-succ x = <→≤ (lemma-half< x)

  {-# TERMINATING #-}
  helper-go : (x gas : ℕ) → x ≤ gas → go x gas ≡ digits x
  helper-go zero zero z≤n = refl
  helper-go zero (succ gas) z≤n = refl
  helper-go (succ x) zero ()
  helper-go (succ x) (succ gas) (s≤s p) =
    cong succ (trans (helper-go (half (succ x)) gas (lemma-≤ {x} {gas} p)) lemma-right)
      where
      lemma-right : go (half (succ x)) (half (succ x)) ≡ go (half (succ x)) x
      lemma-right = symm (helper-go (half (succ x)) x (lemma-half-succ x))
--                                  ^^^^^^^^^^^^^^^ ^


  -- EXERCISE: Verify this basic statement, certifying that the function meets its contract.
  -- (Not easy, you will need auxiliary lemmas!)
  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = begin
    digits (succ n)
      ≡⟨⟩
    go (succ n) (succ n)
      ≡⟨ cong succ (helper-go (half (succ n)) n (lemma-half-succ n)) ⟩
    succ (digits (half (succ n))) ∎


-- ───────────────────────────────────────────────────────
-- ────[ WELL_FOUNDED RECURSION WITH NATURAL NUMBERS ]────
-- ───────────────────────────────────────────────────────

module WfNat where
  data Acc : ℕ → Set where
    acc : {x : ℕ} → ((y : ℕ) → y < x → Acc y) → Acc x

  -- EXERCISE: Show that every natural number is accessible.
  theorem-ℕ-well-founded : (n : ℕ) → Acc n
  theorem-ℕ-well-founded zero    =  acc (λ { m () })
  theorem-ℕ-well-founded (succ n) = acc (λ m m<sn → aux m m<sn (theorem-ℕ-well-founded n))
    where
    aux : (m : ℕ) → m < succ n → Acc n → Acc m
    aux .n base (acc f) = acc f
    aux m (step m<n) (acc f) = f m m<n

  go : (n : ℕ) → Acc n → ℕ
  go zero     gas     = zero
  go (succ n) (acc f) = succ (go (half (succ n)) (f (half (succ n)) (lemma-half< n)))

  digits : ℕ → ℕ
  digits n = go n (theorem-ℕ-well-founded n)

  lemma-go-extensional : (n : ℕ) (p q : Acc n) → go n p ≡ go n q
  lemma-go-extensional zero     p       q       = refl
  lemma-go-extensional (succ n) (acc f) (acc g) = cong succ (lemma-go-extensional (half (succ n)) _ _)

  -- EXERCISE: Verify this fundamental observation. Not easy!
  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = begin
    digits (succ n)                                                    ≡⟨⟩
    go (succ n) (theorem-ℕ-well-founded (succ n))                      ≡⟨⟩
    succ (go (half (succ n)) _)                                        ≡⟨ cong succ (lemma-go-extensional (half (succ n)) _ _) ⟩
    succ (go (half (succ n)) (theorem-ℕ-well-founded (half (succ n)))) ≡⟨⟩
    succ (digits (half (succ n)))                             ∎


  data G : ℕ → ℕ → Set where
    -- cf. naive definition: "digits zero = zero"
    base : G zero zero

    -- cf. naive definition: "digits (succ n) = succ (digits (half (succ n)))"
    step : {n y : ℕ} → G (half (succ n)) y → G (succ n) (succ y)

  -- EXERCISE: For a change, this is not too hard.
  lemma-G-is-functional : {a b b' : ℕ} → G a b → G a b' → b ≡ b'
  lemma-G-is-functional base base = refl
  lemma-G-is-functional (step p) (step q) = cong succ (lemma-G-is-functional p q)

  data Σ (X : Set) (Y : X → Set) : Set where
    _,_ : (x : X) → Y x → Σ X Y

  -- EXERCISE: Fill this in. You will need lemma-digits and more; not easy.

  lemma-G-is-computed-by-digits' : (a : ℕ) → Acc a → G a (digits a)
  lemma-G-is-computed-by-digits' zero _ = base
  lemma-G-is-computed-by-digits' (succ a) (acc f) rewrite lemma-digits a
    = step (subst (G (half (succ a))) petit ((lemma-G-is-computed-by-digits' (half (succ a))) (f (half (succ a)) (lemma-half< a))))
      where
      petit : (digits (half (succ a)))
              ≡ (go (half (succ a)) (theorem-ℕ-well-founded (half (succ a))))
      petit = refl

  lemma-G-is-computed-by-digits : (a : ℕ) → G a (digits a)
  lemma-G-is-computed-by-digits a = lemma-G-is-computed-by-digits'
                                    a
                                    (theorem-ℕ-well-founded a)


-- ─────────────────────────────────────────────
-- ────[ WELL_FOUNDED RECURSION IN GENERAL ]────
-- ─────────────────────────────────────────────

module WfGen (X : Set) (_<_ : X → X → Set) where
  data Acc : X → Set where
    acc : {x : X} → ((y : X) → y < x → Acc y) → Acc x

  invert : {x : X} → Acc x → ((y : X) → y < x → Acc y)
  invert (acc f) = f

  -- EXERCISE: Show that well-founded relations are irreflexive. More
  -- precisely, verify the following local version of this statement:
  lemma-wf-irreflexive : {x : X} → Acc x → x < x → ⊥
  lemma-wf-irreflexive {x} (acc f) x<x = lemma-wf-irreflexive (f x x<x) x<x

  -- EXERCISE: Show that there are no infinite descending sequences.
  lemma-no-descending-sequences : (α : ℕ → X) → ((n : ℕ) → α (succ n) < α n) → Acc (α zero) → ⊥
  lemma-no-descending-sequences α desc (acc f) = lemma-no-descending-sequences (λ n → α (succ n)) (λ n → desc (succ n)) (f (α 1) (desc 0))

  module _ {A : X → Set} (step : (x : X) → ((y : X) → y < x → A y) → A x) where
    -- This is a very general "go" function like for the particular "digits" example above.
    -- The goal of this development is to define the function "f"
    -- below and verify its recursion property.
    go : (x : X) → Acc x → A x
    go x (acc f) = step x (λ y p → go y (f y p))

    -- EXERCISE: Show that, assuming that the recursion template "step"
    -- doesn't care about the witnesss of accessibility, so does the
    -- "go" function. The extra assumption is required since in
    -- standard Agda we cannot verify that witnesses of accessibility
    -- are unique.
    module _ (extensional : (x : X) (u v : (y : X) → y < x → A y) → ((y : X) (p : y < x) → u y p ≡ v y p) → step x u ≡ step x v) where

      lemma : (x : X) (p q : Acc x) → go x p ≡ go x q
      lemma x (acc f) (acc g) = extensional x
                                            (λ y p → go y (f y p))
                                            (λ y p → go y (g y p))
                                            λ y p → lemma y (f y p) (g y p)


      -- EXERCISE: Assuming that X is well-founded, we can define the
      -- function "f" below. Verify that this satisfies the desired
      -- recursion equation.
      module _ (wf : (x : X) → Acc x) where
        f : (x : X) → A x
        f x = go x (wf x)

        theorem : (x : X) → f x ≡ step x (λ y p → f y)
        theorem x with wf x
        ... | acc g = begin
                go x (acc g)
                  ≡⟨⟩
                step x (λ y p → go y (g y p))
                  ≡⟨ extensional x (λ y p → go y (g y p)) (λ y p → go y (wf y)) (λ y p → lemma y (g y p) (wf y)) ⟩
                step x (λ y p → go y (wf y))
                  ≡⟨⟩
                step x (λ y p → f y) ∎
