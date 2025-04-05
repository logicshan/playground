
module Refinement where

infix 30 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

infixl 50 _+_
_+_ : ℕ → ℕ → ℕ
0     + n = n
suc m + n = suc (m + n)


s≡s : ∀{m n} → m ≡ n → 1 + m ≡ 1 + n
s≡s refl = refl

n+0≡n : ∀ n → n + 0 ≡ n
n+0≡n zero    = refl
n+0≡n (suc n) = s≡s (n+0≡n n)

infixr 60 _::_
data Vec (A : Set) : ℕ → Set where
  []   : Vec A 0
  _::_ : ∀{n} → A → Vec A n → Vec A (1 + n)

infixr 50 _++_
_++_ : ∀{A m n} → Vec A m → Vec A n → Vec A (m + n)
[]      ++ ys = ys
x :: xs ++ ys = x :: (xs ++ ys)

-- if we want to match against refl : n + 0 ≡ n
-- that match needs to be able to refine some variable.
-- So, we must also match against n + 0, then matching
-- against refl will refine the new variable to n (hence
-- the dot). At the same time, it will refine the
-- n + 0 in the type of v' to n, so we can return it.
--
-- just matching against v ++ [] isn't enough, despite
-- that implicitly having an n + 0 in it. Also, you can't
-- match to turn n into n + 0, since that would be
-- attempting to refine ns into expressions still containing
-- n, which is what we're trying to refine in the first
-- place. And all ns that are in scope during the match
-- get so refined; there's no way to refine some ns but
-- not others.
vid₁ : ∀{n A} → Vec A n → Vec A n
vid₁ {n} v with n + 0 | v ++ [] | n+0≡n n
...  | .n | v' | refl = v'

-- If one uncomments the below and views the things in scope
-- in the hole, he'll see:
--
--  m  : ℕ
--  v' : Vec A m
--  pf : m ≡ n
--
-- So giving a name to n + 0 has replaced all occurrences of
-- it with the new variable. Then, matching pf against refl
-- allows this new variable to be refined, and equated with
-- n, giving things the type we want. Only variables can be
-- refined this way, though. Not more complex expressions
-- (which explains why only using v ++ [] in the with is
-- unacceptable; its type still contains n + 0, instead of a
-- refinable variable).
{-
vid₂ : ∀{n A} → Vec A n → Vec A n
vid₂ {n} v with n + 0 | v ++ [] | n+0≡n n
...  | m | v' | pf = ?
-}