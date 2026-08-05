{-# OPTIONS --universe-polymorphism #-}

-- Using parametricity (with help from LFT) to prove that
-- all elements of (∃ t. t) are equal.

module ParametricTerminal where

open import Level

open import LFT

open import Relation.Binary.PropositionalEquality

postulate
  -- extensional equality of functions
  ext : ∀{i j} → {A : Set i} → {B : A → Set j}
      → (f g : (x : A) → B x)
      → (∀ x → f x ≡ g x)
      → f ≡ g

-- This type will come in handy in a couple places.
K : ∀{i} → Set i → Set (suc zero ⊔ i)
K T = (S : Set) → S → T

[K] : ∀{i} {T : Set i} → [Set i ] T T → [Set suc zero ⊔ i ] (K T) (K T)
[K] [T] = [Π] [Set] λ [S] → [S] [→] [T]

postulate
  -- Postulate parametricity for K
  param-K : ∀{i} {T : Set i} → ([T] : [Set i ] T T) → (h : K T) → [K] [T] h h

-- This is the free theorem according to lambdabot's @free comand.
-- It can be proved with the parametricity axiom above.
free-K : ∀{i} {T : Set i} A B → (f : A → B) → (h : K T)
       → ∀ x → h A x ≡ h B (f x)
free-K A B f h x = lower (param-K (λ x y → Lift (x ≡ y)) h
                                  (λ y z → f y ≡ z) refl)

-- This is a special case of the above free theorem. All terms with type
-- K T are constant functions.
const-K : ∀{i} {T : Set i} → (h : K T) → (S₁ S₂ : Set) → (x : S₁) (y : S₂)
        → h S₁ x ≡ h S₂ y
const-K h S₁ S₂ x y = free-K S₁ S₂ (λ _ → y) h x

module Church where
  -- ∃ t. t is isomorphic to ∀ r. (∀ t. t → r) → r
  ∃! : Set₁
  ∃! = (R : Set) → ((S : Set) → S → R) → R

  [∃!] : [Set1] ∃! ∃!
  [∃!] = [Π] [Set] λ [R] → ([Π] [Set] λ [S] → [S] [→] [R]) [→] [R]

  postulate
    -- Parametricity for the encoding of ∃ t. t
    param-∃! : ∀ w → [∃!] w w

  -- Again, the free theorem according to lambdabot, proved with
  -- the fancier parametricity.
  free-∃! : ∀ A B → (f : A → B) → (k₁ : K A) → (k₂ : K B)
          → (∀ S₁ S₂ → (g : S₁ → S₂) → (z : S₁) → f (k₁ S₁ z) ≡ k₂ S₂ (g z))
          → (w : ∃!)
          → f (w A k₁) ≡ w B k₂
  free-∃! A B f k₁ k₂ coh w = param-∃! w (λ x y → f x ≡ y)
                                (λ {S₁} {S₂} _~_ {x} {y} x~y
                                    → coh S₁ S₂ (λ _ → y) x)

  -- A handy special case of the free theorem.
  lemma-∃! : (R : Set) (w : ∃!) (k : K R) → k R (w R k) ≡ w R k
  lemma-∃! R w k = free-∃! R R (k R) k k
                           (λ S₁ S₂ g z → const-K k R S₂ (k S₁ z) (g z))
                           w

  -- All elements of (∃ t. t) are the same.
  ∃!-single : ∀(w₁ w₂ : ∃!) → w₁ ≡ w₂
  ∃!-single w₁ w₂ = ext w₁ w₂ λ R
                  → ext (w₁ R) (w₂ R) λ k
                  → let open ≡-Reasoning 
                     in begin 
                          w₁ R k
                        ≡⟨ sym (lemma-∃! R w₁ k)  ⟩
                          k R (w₁ R k)
                        ≡⟨ const-K k R R (w₁ R k) (w₂ R k) ⟩
                          k R (w₂ R k)
                        ≡⟨ lemma-∃! R w₂ k ⟩
                          w₂ R k
                        ∎

module Data where
  -- Use a datatype instead.
  data ∃! : Set₁ where
    _,_ : (S : Set) (x : S) → ∃!

  -- The constructor has type K ∃!, so it is a constant function,
  -- according to the theorem at the top.
  const-, : ∀ S T → (x : S) (y : T) → (S , x) ≡ (T , y)
  const-, = const-K _,_

  -- Since every element of ∃! is of the form (S , x), and _,_ is
  -- a constant function, every element is the same.
  ∃!-single : ∀(w₁ w₂ : ∃!) → w₁ ≡ w₂
  ∃!-single (S , x) (T , y) = const-, S T x y
