{-# OPTIONS --irrelevant-projections #-}

module StateAlgebra where

open import Data.Empty
open import Data.Product
open import Data.Unit

open import Function

open import Relation.Binary.PropositionalEquality

postulate
  ext : ∀{A B : Set} (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g

-- Representations of computations with a mutable cell of type S.
-- The effectful operations are get and put, and the operations
-- obey the specified laws.
record _Cell (S : Set) : Set₁ where
  field
    Carrier : Set
    get     : (S → Carrier) → Carrier
    put     : S → Carrier → Carrier

    .law₁ : ∀{s t v} → put s (put t v) ≡ put t v
    .law₂ : ∀{v}     → get (λ s → put s v) ≡ v
    .law₃ : ∀{k : S → S → Carrier}
          → get (λ s → get (λ t → k s t)) ≡ get (λ s → k s s)
    .law₄ : ∀{s k} → put s (get k) ≡ put s (k s)
    .law₅ : ∀{v}     → get (λ _ → v) ≡ v

open _Cell

-- Morphisms of S Cells
record _⇥_ {S} (X Y : S Cell) : Set where
  field
    morph : Carrier X → Carrier Y

    .pres₁ : ∀{k}   → get Y (λ s → morph (k s)) ≡ morph (get X k)
    .pres₂ : ∀{s v} → put Y s (morph v) ≡ morph (put X s v)

open _⇥_

-- The forgetful functor.
U : ∀{S} → S Cell → Set
U = Carrier

mapU : ∀{S} {X Y : S Cell} → (X ⇥ Y) → U X → U Y
mapU = morph

-- The allegedly free functor.
F : ∀{S} → Set → S Cell
F {S} A = record { Carrier = S → S × A
                 ; get     = λ k s → k s s
                 ; put     = λ s k _ → k s
                 ; law₁    = refl
                 ; law₂    = refl
                 ; law₃    = refl
                 ; law₄    = refl
                 ; law₅    = refl
                 }

mapF : ∀{S} {A B : Set} → (A → B) → F {S} A ⇥ F B
mapF f = record { morph = λ k s → map id f (k s)
                ; pres₁ = refl
                ; pres₂ = refl
                }

pure : ∀{S A} → A → S → S × A
pure x s = (s , x)

-- The isomorphisms witnessing the adjunction
♯ : ∀{S A} {Y : S Cell} → (F A ⇥ Y) → (A → U Y)
♯ m x = morph m (pure x)

♭-aux : ∀{S A} {Y : S Cell} → (S → S × A) → (A → Carrier Y) → (S → Carrier Y)
♭-aux {S} {A} {Y} g f s = put Y (proj₁ (g s)) (f (proj₂ (g s)))

♭ : ∀{S A} {Y : S Cell} → (A → U Y) → (F A ⇥ Y)
♭ {S} {A} {Y} f = record { morph = λ g → get Y (k g f)
                         ; pres₁ = law₃ Y
                         ; pres₂ = lemma₁
                         }
 where
 open ≡-Reasoning

 k = ♭-aux {S} {A} {Y}

 lemma₀ : ∀{s : S} {g : S → S × A}
        → (λ _ → k (λ _ → g s) f s) ≡ (λ(t : S) → k (λ _ → g s) f t)
 lemma₀ = refl

 .lemma₁ : ∀{s} {g} → put Y s (get Y (k g f)) ≡ get Y (k (λ _ → g s) f)
 lemma₁ {s} {g} = begin
                    put Y s (get Y (k g f))
                  ≡⟨ law₄ Y ⟩
                    put Y s (k g f s)
                  ≡⟨ refl ⟩
                    put Y s (put Y (proj₁ (g s)) (f (proj₂ (g s))))
                  ≡⟨ law₁ Y ⟩
                    put Y (proj₁ (g s)) (f (proj₂ (g s)))
                  ≡⟨ refl ⟩
                    k (λ _ → g s) f s
                  ≡⟨ sym (law₅ Y) ⟩
                    get Y (λ _ → k (λ _ → g s) f s)
                  ≡⟨ cong (λ h → get Y h) (lemma₀ {s} {g}) ⟩
                    get Y (k (λ _ → g s) f)
                  ∎

-- proofs that they are isomorphisms                   
.iso₁ : ∀{S A} {Y : S Cell} (f : A → U Y) → ♯ (♭ {S} {A} {Y} f) ≡ f
iso₁ {S} {A} {Y} f = begin
                       (λ x → get Y (λ s → put Y s (f x)))
                     ≡⟨ ext (λ x → get Y (λ s → put Y s (f x)))
                            f (λ _ → law₂ Y) ⟩
                       (λ x → f x)
                     ∎
 where
 open ≡-Reasoning

eq-morph : ∀{S} {X Y : S Cell}
         → (f g : Carrier X → Carrier Y)
         → (pf₁ : ∀{k} → get Y (λ s → f (k s)) ≡ f (get X k))
         → (pg₁ : ∀{k} → get Y (λ s → g (k s)) ≡ g (get X k))
         → (pf₂ : ∀{s v} → put Y s (f v) ≡ f (put X s v))
         → (pg₂ : ∀{s v} → put Y s (g v) ≡ g (put X s v))
         → f ≡ g
         → _≡_ {A = X ⇥ Y}
               (record { morph = f ; pres₁ = pf₁ ; pres₂ = pf₂ })
               (record { morph = g ; pres₁ = pg₁ ; pres₂ = pg₂ })
eq-morph f .f _ _ _ _ refl = refl


.iso₂ : ∀{S A} {Y : S Cell} (m : F A ⇥ Y) → ♭ {S} {A} {Y} (♯ m) ≡ m
iso₂ {S} {A} {Y} m = eq-morph {S} {F A} {Y}
                              (morph n) (morph m)
                              (pres₁ n) (pres₁ m)
                              (pres₂ n) (pres₂ m) lemma₂
 where
 open ≡-Reasoning

 n : F A ⇥ Y
 n = ♭ {S} {A} {Y} (♯ m)

 f : (S → S × A) → Carrier Y
 f = morph m

 p₁ : ∀(k : S → S → S × A) → get Y (λ s → f (k s)) ≡ f (λ s → k s s)
 p₁ k = pres₁ m

 p₂ : ∀ s v → put Y s (f v) ≡ f (λ _ → v s)
 p₂ s v = pres₂ m

 lemma₀ : ∀ g s → ♭-aux {S} {A} {Y} g (♯ m) s ≡ f (λ _ → g s)
 lemma₀ g s = p₂ (proj₁ (g s)) (pure (proj₂ (g s)))

 lemma₁ : ∀ g → get Y (λ s → f (λ _ → g s)) ≡ f g
 lemma₁ g = p₁ (λ s _ → g s)

 lemma₂ : morph n ≡ f
 lemma₂ = ext (morph n) f λ g
        → begin
            morph n g
          ≡⟨ cong (get Y) (ext (♭-aux {S}{A}{Y} g (♯ m))
                               (λ s → f (λ _ → g s)) (lemma₀ g)) ⟩
            get Y (λ s → f (λ _ → g s))
          ≡⟨ lemma₁ g ⟩
            f g
          ∎

-- Thus, F ⊣ U

State : Set → Set → Set
State S A = U (F {S} A)

-- State S is the free S Cell monad over a type A.
