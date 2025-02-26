{-# OPTIONS --cubical #-}

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1

f : S¹ → S¹
f base = base
f (loop i) = loop i

p : base ≡ base
p i = loop i

q : base ≡ base
q i = loop ( ~ i )

{-
Square : ∀ {ℓ} {A : Set ℓ} {x0 x1 y0 y1 : A} →
           x0 ≡ x1 → y0 ≡ y1 → x0 ≡ y0 → x1 ≡ y1 → Set ℓ
Square p q r s = PathP (λ i → p i ≡ q i) r s
-}

s : Square refl q p refl
s i j = p (i ∧ ( ~ j ) )

--    j ^
--      |
--      ---> i

--              refl
--      base------------base
--       | ############# |
--       | ############# |
--  refl | ############# |q
--       | ############# |
--       | ############# |
--       | ############# |
--      base------------base
--               p

p∙q : base ≡ base
p∙q i = hcomp (λ j → λ { (i = i0) → base
                       ; (i = i1) → q j
                       })
              (p i)

--              p∙q
--      base------------base
--       |               |
--       |               |
--  refl |               |q
--       |               |
--       |               |
--       |               |
--      base------------base
--               p

filler : Square refl q p p∙q
filler i j = hfill (λ j → λ { (i = i0) → base
                            ; (i = i1) → q j
                            })
                   (inS (p i)) j

i=i1 : Square q refl q refl
i=i1 j k = q (j ∨ k)

refl≡p∙q : refl ≡ p∙q
refl≡p∙q j i = hcomp (λ k → λ { (i = i0) → base
                              ; (i = i1) → s (~ j) k
                              ; (j = i0) → s i k
                              ; (j = i1) → p∙q i
                              })
                     (filler i j)



-- k
-- ^   j
-- |  ^
-- | /
-- |/
-- -------> i



--            _____p∙q______
--           /|            /|
--          / |           / |
--         /____refl_____/  |
--         |  |          |  |
--         |  |_________ |__|
--         | /           |  /
--         |/            | /
--         -------------- /
