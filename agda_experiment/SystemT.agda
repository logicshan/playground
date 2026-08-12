module SystemT where
 
data Bool : Set where
  true  : Bool
  false : Bool
 
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
 
if_then_else_ : {C : Set} → Bool → C → C → C
if true  then x else y = x
if false then x else y = y
 
natrec : {C : Set} → C → (ℕ → C → C) → ℕ → C
natrec p h  zero    = p
natrec p h (succ n) = h n (natrec p h n)

_+_ : ℕ → ℕ → ℕ
_+_ n m = natrec m (λ _ y → succ y) n
 
_*_ : ℕ → ℕ → ℕ
_*_ n m = natrec zero (λ _ y → y + m) n

pred : ℕ → ℕ
pred = natrec zero (λ x _ → x)
 
_-_ : ℕ → ℕ → ℕ
_-_ n = natrec n (λ _ y → (pred y))

¬ : Bool → Bool
¬ b = if b then false else true
 
_∧_ : Bool → Bool → Bool
a ∧ b = if a then b else false
 
_∨_ : Bool → Bool → Bool
a ∨ b = if a then true else b
 
_⊕_ : Bool → Bool → Bool
a ⊕ b = if a then (¬ b) else b

equalityBool : Bool → Bool → Bool
equalityBool a b = if a then (a ∧ b) else (¬ b)

isZero : ℕ → Bool
isZero = natrec true (λ _ _ → false)

pair : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ
pair a b = λ f → f a b

fst : ((ℕ → ℕ → ℕ) → ℕ) → ℕ
fst p = p (λ a _ → a)

snd : ((ℕ → ℕ → ℕ) → ℕ) → ℕ
snd p = p (λ _ b → b)

fib : ℕ → ℕ
fib n = fst
          (natrec
            (pair zero (succ zero))
            (λ k p →
              pair
                (snd p)
                (fst p + snd p))
            n)

min : ℕ → ℕ → ℕ
min m n = m - (m - n)
