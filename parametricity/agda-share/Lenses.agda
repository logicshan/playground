{-# OPTIONS --universe-polymorphism --irrelevant-projections #-}

module Lenses where

open import Level

open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

import Relation.Binary.HeterogeneousEquality as HEq

postulate
  ext : ∀{i j} {A : Set i} {B : A → Set j}
         (f g : (x : A) → B x) → (∀ x → f x ≡ g x) → f ≡ g

-- Consider the category with objects I-pointed types, meaning a type together
-- with a I-getter and I-setter that satisfy the natural laws.
--
-- Note: the dotted fields (and dotted top-level definitions later) are
-- irrelevant, so that proving two I-pointed types (etc.) equal doesn't
-- require proving the coherence proofs equal.
record _Pointed (I : Set) : Set₁ where
  field
    Carrier : Set
    get     : Carrier → I
    set     : Carrier → I → Carrier

    .law₁    : ∀ x z     → get (set x z)     ≡ z
    .law₂    : ∀ x       → set x (get x)     ≡ x
    .law₃    : ∀ x z₁ z₂ → set (set x z₁) z₂ ≡ set x z₂

open _Pointed

-- Morphisms between I-pointed types are functions on the carriers that preserve
-- the points, meaning they commute with the observations of the points.
record _⇥_ {I} (X Y : I Pointed) : Set where
  field
    morph : Carrier X → Carrier Y

    .pres₁ : ∀ x   → get Y (morph x)   ≡ get X x
    .pres₂ : ∀ x z → set Y (morph x) z ≡ morph (set X x z)

open _⇥_

-- There is a functor U from this category to the category of types, which
-- simply forgets the pointed structure.
U : ∀{I} → I Pointed → Set
U = Carrier

mapU : ∀{I} {X Y : I Pointed} → (X ⇥ Y) → U X → U Y
mapU = morph

-- There is also a functor C from the category of types to the category of
-- I-pointed types, taking A to the cofree I-pointed type over A, to be proved.
C : ∀{I} → Set → I Pointed
C {I} A = record
        { Carrier = I × (I → A)
        ; get     = proj₁
        ; set     = λ p x → (x , proj₂ p)
        ; law₁    = λ _ _   → refl
        ; law₂    = λ _     → refl
        ; law₃    = λ _ _ _ → refl
        }

mapC : ∀{I A B} → (A → B) → (C {I} A ⇥ C B)
mapC {I} {A} {B} f = record
                   { morph = map id (_∘_ f)
                   ; pres₁ = λ _   → refl
                   ; pres₂ = λ _ _ → refl
                   }

extract : ∀{I B : Set} → I × (I → B) → B
extract (x , f) = f x

-- C being cofree means that it should be right-adjoint to U. This means there
-- should be a natural isomorphism between (U X → B) and (X ⇥ C B).
♯ : ∀{I B} {X : I Pointed} → (U X → B) → (X ⇥ C B)
♯ {I} {B} {X} f = record
                { morph = λ x → (get X x , f ∘ set X x)
                ; pres₁ = λ _ → refl
                ; pres₂ = λ x z →
                    begin
                      (z , f ∘ set X x)
                    ≡⟨ cong (λ w → (w , f ∘ set X x)) (sym (law₁ X x z)) ⟩
                      (get X (set X x z) , f ∘ set X x)
                    ≡⟨ cong (λ h → (get X (set X x z) , h)) lemma₁ ⟩
                      (get X (set X x z) , (λ w → f (set X (set X x z) w)))
                    ∎
                }
 where
 .lemma₁ : ∀{x : Carrier X} {z : I}
         → _≡_ {A = I → B} (λ w → f (set X x w)) (λ w → f (set X (set X x z) w))
 lemma₁ {x} {z} = ext (λ w → f (set X x w))
                      (λ w → f (set X (set X x z) w))
                      (λ w → cong (λ v → f v) (sym (law₃ X x z w)))

♭ : ∀{I B} {X : I Pointed} → (X ⇥ C B) → (U X → B)
♭ {I} {B} {X} h = extract ∘ morph h

.iso₁ : ∀{I B} {X : I Pointed} → (f : U X → B)
      → ♭ {I} {B} {X} (♯ {I} {B} {X} f) ≡ f
iso₁ {I} {B} {X} f = ext (λ x → f (set X x (get X x))) f λ x →
                         cong (λ v → f v) (law₂ X x)

lemma₂ : ∀{I B} {X : I Pointed}
          (f₁ f₂ : Carrier X → I × (I → B))
          (p₁₁ : ∀ x → get (C B) (f₁ x) ≡ get X x)
          (p₁₂ : ∀ x → get (C B) (f₂ x) ≡ get X x)
          (p₂₁ : ∀ x z → set (C B) (f₁ x) z ≡ f₁ (set X x z))
          (p₂₂ : ∀ x z → set (C B) (f₂ x) z ≡ f₂ (set X x z))
         → f₁ ≡ f₂
         → _≡_ {A = X ⇥ C B}
             (record { morph = f₁ ; pres₁ = p₁₁ ; pres₂ = p₂₁ })
             (record { morph = f₂ ; pres₁ = p₁₂ ; pres₂ = p₂₂ })
lemma₂ f₁ .f₁ p₁₁ p₁₂ p₂₁ p₂₂ refl = refl


.iso₂ : ∀{I B} {X : I Pointed} → (h : X ⇥ C B) → ♯ {I} {B} {X} (♭ h) ≡ h
iso₂ {I} {B} {X} h = lemma₂ {X = X}
                            f                             (morph h)
                            (λ _ → refl)                  (pres₁ h)
                            (pres₂ (♯ {I} {B} {X} (♭ h))) (pres₂ h)
                            lemma₄
 where
 f : Carrier X → I × (I → B)
 f x = (get X x , λ w → extract (morph h (set X x w)))

 sett : (I × (I → B)) → I → (I × (I → B))
 sett p x = (x , proj₂ p)

 lemma₃ : ∀(x : Carrier X)
        → (λ w → proj₂ (morph h x) w) ≡ (λ w → extract (morph h (set X x w)))
 lemma₃ x = ext (proj₂ (morph h x)) (λ w → extract (morph h (set X x w))) λ w
          → begin
              proj₂ (morph h x) w
            ≡⟨ refl ⟩
              proj₂ (morph h x) (proj₁ (sett (morph h x) w))
            ≡⟨ refl ⟩
              proj₂ (sett (morph h x) w) (proj₁ (sett (morph h x) w))
            ≡⟨ cong (λ v → extract v) (pres₂ h x w) ⟩
              proj₂ (morph h (set X x w)) (proj₁ (morph h (set X x w)))
            ∎

 lemma₄ : f ≡ morph h
 lemma₄ = ext f (morph h) λ x
        → sym (begin
                 morph h x
              ≡⟨ refl ⟩
                 (get (C B) (morph h x) , proj₂ (morph h x))
              ≡⟨ cong (λ v → (v , proj₂ (morph h x))) (pres₁ h x) ⟩
                 (get X x , proj₂ (morph h x))
              ≡⟨ cong (λ g → (get X x , g)) (lemma₃ x) ⟩
                 (get X x , λ w → extract (morph h (set X x w)))
              ∎)

-- Done. U ⊣ C, and so C is the cofree I-pointed type functor. Composing to
-- get a comonad, we get:

Selection : Set → Set → Set
Selection I A = U {I} (C A)

-- The cofree I-pointed type comonad. And the coalgebras of this comonad
-- correspond to the I-pointed types we began with. The actions of those
-- coalgebras are the lenses A → Selection I A, which allow us to observe an
-- I-pointed type A via embedding into the cofree I-pointed type over A.