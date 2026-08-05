
module Cylinder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open Iso

open import Cubical.Data.Sigma

variable
  ℓ : Level

-- The interval has distinguished points zero and one and a path
-- between them.
data [0,1] : Type where
  zero one : [0,1]
  seg : Path [0,1] zero one

-- The cylinder is the product of a space with the interval
Cylinder : Type ℓ → Type ℓ
Cylinder X = X × [0,1]

-- The interval is contractible
[0,1]-lemma : ∀ i → Path [0,1] zero i

-- The path from `zero` to `zero` is just a constant function
-- of the parameter `k`
[0,1]-lemma zero = λ k → zero

-- The path from `zero` to `one` is `seg`
[0,1]-lemma one  = λ k → seg k

[0,1]-lemma (seg j) = λ k → seg (j ∧ k)
-- ^ `j ∧ k` is the 'minimum' of the two parameters, so
-- `λ k → seg (j ∧ k)` is a path parameterized by `k`
-- that goes from:
--   seg (j ∧ 0) = seg 0 = zero
-- to:
--   seg (j ∧ 1) = seg j
-- Showing that there is a path from `zero` to any point
-- along `seg` (parameterized by `j`).
--
-- This path also agrees with the other two. When `j = 0`:
--   seg (j ∧ k) = seg (0 ∧ k) = seg 0 = zero
-- So it is the constantly zero path. When `j = 1`:
--   seg (j ∧ k) = seg (1 ∧ k) = seg k

-- The cylinder on X is homotopic to X. We can exhibit a
-- pair of inverse-up-to-path mappings between them.
lemma : ∀(X : Type ℓ) → Cylinder X ≡ X
lemma X = isoToPath λ where
  .fun (x , i) → x
  .inv x → x , zero

  -- Path X (fun (inv x)) x
  .rightInv x → refl

  -- Path (Cylinder X) (inv (fun (x,i))) (x,i)
  .leftInv (x , i) → λ j → (x , [0,1]-lemma i j)

-- This works for the circle of course:

-- The circle has a distinguished point with a loop path.
data 𝕊¹ : Type where
  base : 𝕊¹
  loop : Path 𝕊¹ base base

circ-lemma : Cylinder 𝕊¹ ≡ 𝕊¹
circ-lemma = lemma 𝕊¹

