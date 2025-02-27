{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

private
  variable
    A B : Type _

subst' : (C : A → Type) → ∀ {x y : A} → x ≡ y → C x → C y
subst' C p c = transp (λ i → C (p i)) i0 c  

{-  
    T : I → Type  r : I  r = i1 |- T constant  t : T i0  
    ----------------------------------------------------
    transp T r t : T i1

    transp T i1 t = t  

-}  

subst'-ref1 : (C : A → Type) → ∀ {x} → (c : C x) → subst' C refl c ≡ c  
subst'-ref1 C {x} c i = transp (λ i → C x) i c

subst'-over : (C : A → Type) → ∀ {x y} → (c : C x) (p : x ≡ y)
              → PathP (λ i → C (p i)) c (subst' C p c)
subst'-over C {x} c p j = transp (λ i → C (p (i ∧ j))) (~ j) c
--                                                     ^^^^^
-- ~ j = i1  <=> j = i0
-- (λ i → C (p (i ∧ j)))
-- (λ i → C (p (i ∧ i0)))
-- (λ i → C (p i0))
-- (λ i → C x)               is constant
