{-# OPTIONS --type-in-type #-}
open import Agda.Primitive
record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field fst : A
        snd : B fst

data _≡_ {i} {A : Set i} (x : A) : A → Set i where
  refl : x ≡ x

{-
-- We have seen:
--   - The initial model (the syntax of type theory)
--   - The set model/standard model
--
-- Family model    Fam
--   Part of a family of models : presheaf models
--   The standard model is also a presheaf model
--
-}

-- All components of the family model : (x₀ , x₁)
--   the components -₀ are the same as in the standard model.

record Con : Set₁ where
  constructor _,_
  field Γ₀ : Set
        Γ₁ : Γ₀ → Set -- Γ₁ : Γ₀ → Prop

record Sub (Γ Δ : Con) : Set₁ where
  constructor _,_
  open Con Γ; Δ₀ = Δ .Con.Γ₀; Δ₁ = Δ .Con.Γ₁
  field σ₀ : Γ₀ → Δ₀                        -- This is a function
        σ₁ : (γ₀ : Γ₀) → Γ₁ γ₀ → Δ₁ (σ₀ γ₀) -- This says that σ₀ is compatible with Γ₁ and Δ₁

record Ty (Γ : Con) : Set₁ where
  constructor _,_
  open Con Γ
  field A₀ : Γ₀ → Set
        A₁ : (γ₀ : Γ₀) (γ₁ : Γ₁ γ₀) → A₀ γ₀ → Set -- A₁ : ___ → Prop

record Tm (Γ : Con) (A : Ty Γ) : Set where
  constructor _,_
  open Con Γ; open Ty A
  field a₀ : (γ₀ : Γ₀) → A₀ γ₀
        a₁ : (γ₀ : Γ₀) (γ₁ : Γ₁ γ₀) → A₁ γ₀ γ₁ (a₀ γ₀)

-- We can define id, _∘_, substitution operations, etc.
--
-- Example: context extension

_▷_ : (Γ : Con) → Ty Γ → Con
(Γ₀ , Γ₁) ▷ (A₀ , A₁) = (Σ Γ₀ λ γ₀ → A₀ γ₀)
                         -- Set of pairs (γ₀ , a₀) where γ₀ : Γ₀, a₀ : A₀ γ₀
                      , λ (γ₀ , a₀) → Σ (Γ₁ γ₀) λ γ₁ → A₁ γ₀ γ₁ a₀
                         -- Family over (γ₀ , a₀) of pairs (γ₁ , a₁) where γ₁ : Γ₁ γ₀, a₁ : A₁ γ₀ γ₁ a₀

-- Empty set
data 𝟘 : Set where

-- Empty family
⊥ : ∀ {Γ} → Ty Γ
⊥ = (λ γ₀ → 𝟘)
  , (λ γ₀ γ₁ ())

-- Unit set
record 𝟙 : Set where
  constructor tt

⋄ : Con
⋄ = 𝟙 , (λ x → 𝟙)

-- Unit family
⊤ : ∀ {Γ} → Ty Γ
⊤ = (λ γ₀ → 𝟙)
  , (λ γ₀ γ₁ x → 𝟙)

-- Boolean set
data 𝟚 : Set where
  𝟚-true  : 𝟚
  𝟚-false : 𝟚

-- Boolean family
Bool : ∀ {Γ} → Ty Γ
Bool = (λ γ₀ → 𝟚)
     , (λ γ₀ γ₁ x → 𝟙)

-- Equivalent to
-- Bool' : ∀ {Γ} → Ty Γ
-- Bool' = (λ γ₀ → 𝟚)
--       , (λ γ₀ γ₁ x → Σ 𝟚 (λ b → b ≡ x))

true : ∀ {Γ} → Tm Γ Bool
true = (λ _ → 𝟚-true) , (λ _ _ → tt)

false : ∀ {Γ} → Tm Γ Bool
false = (λ _ → 𝟚-false) , (λ _ _ → tt)

-- Any type of the standard model gives a type of the family model
FromSet : (Γ : Con) (A : Γ .Con.Γ₀ → Set) → Ty Γ
FromSet Γ A = (λ γ₀ → A γ₀) , λ γ₀ γ₁ x → 𝟙

-- Bool ~ FromSet 𝟚, ⊤ ~ FromSet 𝟙, ⊥ ~ FromSet 𝟘

-- Type not of the form FromSet X
-- A : ∀ {Γ} → Ty Γ
-- A = (λ _ → 𝟙) , λ γ₀ γ₁ x → 𝟘

-- The law of excluded middle does not hold for A in the family model
-- LEM : A ∨ ¬A

-- There is no term  lem : Tm ⋄ (A + (¬ A))
-- Informally: lem should make the same choice between A and ¬ A at
--   both levels.

-- Sum types in the metatheory:
data _⊎_ (A : Set) (B : Set) : Set where
  injₗ : A → A ⊎ B
  injᵣ : B → A ⊎ B


-- Sum types:
+₁ : ∀ {Γ} (A : Ty Γ) (B : Ty Γ) → ∀ γ₀ (γ₁ : Γ .Con.Γ₁ γ₀)
   → A .Ty.A₀ γ₀ ⊎ (B .Ty.A₀ γ₀) → Set
+₁ (_ , A₁) (_ , B₁) γ₀ γ₁ (injₗ x) = A₁ γ₀ γ₁ x
+₁ (_ , A₁) (_ , B₁) γ₀ γ₁ (injᵣ x) = B₁ γ₀ γ₁ x

_+_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ
(A₀ , A₁) + (B₀ , B₁) = (λ γ₀ → A₀ γ₀ ⊎ B₀ γ₀) , +₁ (A₀ , A₁) (B₀ , B₁)
-- We have Bool ≃ (⊤ + ⊤)

_⇒_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ
(A₀ , A₁) ⇒ (B₀ , B₁)
  = (λ γ₀       →  A₀ γ₀ → B₀ γ₀)
  , (λ γ₀ γ₁ f₀ →  (a₀ : A₀ γ₀) (a₁ : A₁ γ₀ γ₁ a₀) → B₁ γ₀ γ₁ (f₀ a₀))

¬ : ∀ {Γ} → Ty Γ → Ty Γ
¬ A = A ⇒ ⊥

A : ∀ {Γ} → Ty Γ
A = (λ _ → 𝟙) , λ γ₀ γ₁ x → 𝟘

-- Attempting to define lem
lem : Tm ⋄ (A + (¬ A))
-- lem = (λ γ₀ → ?0) , ?
--   In ?0, we have to choose between A₀ and ¬ A₀.
--   We are forced to pick A₀.
-- lem = (λ γ₀ → injₗ tt) , λ γ₀ γ₁ → ?1
--   ?1 should be an inhabitant of 𝟘.
lem = (λ γ₀ → injₗ tt) , λ γ₀ γ₁ → {!!}


-- We can prove in the metatheory that there is no term
--   in Tm ⋄ (A + (¬ A)).

notLem' : (a₀ : 𝟙 ⊎ (𝟙 → 𝟘)) (a₁ : +₁ {Γ = ⋄} A (¬ A) tt tt a₀) → 𝟘
notLem' (injₗ _) a₁ = a₁
notLem' (injᵣ x) _ = x tt

notLem : Tm ⋄ (A + (¬ A)) → 𝟘
notLem (a₀ , a₁) = notLem' (a₀ tt) (a₁ tt tt)

-- This implies that LEM is not provable in the syntax of type theory.

-- Universe in the family model
U : ∀ {Γ} → Ty Γ
U = (λ γ₀ → Set) , (λ γ₀ γ₁ A → (A → Set))

El : ∀ {Γ} → Tm Γ U → Ty Γ
El (A₀ , A₁) = (λ γ₀ → A₀ γ₀) , (λ γ₀ γ₁ a₀ → A₁ γ₀ γ₁ a₀)

Π : ∀ {Γ} → (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
Π (A₀ , A₁) (B₀ , B₁)
  = (λ γ₀       →  (a₀ : A₀ γ₀) → B₀ (γ₀ , a₀))
  , (λ γ₀ γ₁ f₀ →  (a₀ : A₀ γ₀) (a₁ : A₁ γ₀ γ₁ a₀)
                   → B₁ (γ₀ , a₀) (γ₁ , a₁) (f₀ a₀))

q : Tm (⋄ ▷ U) U
Tm.a₀ q γ₀ = γ₀ .Σ.snd
Tm.a₁ q γ₀ γ₁ = γ₁ .Σ.snd

id : Tm ⋄ (Π U (El q ⇒ El q))
id = (λ γ₀ a₀ x → x)
   , (λ γ₀ γ₁ a₀ a₁ a₂ a₃ → a₃)

-- parametricity : (f : Tm ⋄ (Π U (El q ⇒ El q)))
--                 (A : Tm ⋄ U) (x : Tm ⋄ (El A))
--               → (f $ A $ x)₀ ≡ x₀

-- proof: we apply f to A'
--   A'₀   = A₀
--   A'₁ a = (a ≡ x)
--
--  we have x' : Tm ⋄ (El A')
--   x'₀ = x₀
--   x'₁ = refl
--
--  the component -₁ of (f $ A' $ x') will be a proof
--       of A'₁ (f $ A' $ x')₀
--    i.e. a proof of ((f $ A $ x)₀ ≡ x)

-- Consequence of this proof: any function with the type of
--   the polymorphic identity function defined in the syntax Syn
--   becomes the identity function in the standard model Set.
--
-- By initiality of the syntax:
--   ⟦_⟧ : Syn → Fam
--   (-)₀ : Fam → Set
--   [_] : Syn → Set     [ x ] = ⟦ x ⟧₀
--
-- f   : Syn.Tm ⋄ (Π U (El q ⇒ El q))
-- ⟦f⟧ : Fam.Tm ⋄ (Π U (El q ⇒ El q))
-- [f] : Set.Tm ⋄ (Π U (El q ⇒ El q))
--
-- Parametricity for ⟦f⟧   ⇒   [f] is the identity function.

-- Variants / extensions of the family model
record Con' : Set₁ where
  constructor _,_
  field Γ₀ : Set
        Γ₁ : Γ₀ → Set
        Γ₂ : (γ₀ : Γ₀) → Γ₁ γ₀ → Set

-- This model is related to binary parametricity
record Con'' : Set₁ where
  constructor _,_
  field Γ₀ : Set
        Γ₁ : Γ₀ → Γ₀ → Set

-- Reflexive graph model
record Con''' : Set₁ where
  constructor _,_
  field Γ₀ : Set
        Γ₁ : Γ₀ → Γ₀ → Set
        r  : ∀ γ₀ → Γ₁ γ₀ γ₀

-- Alternative definition of the family model
record Con'''' : Set₁ where
  constructor _,_,_
  field Γ₀ : Set
        Γ₁ : Set
        f  : Γ₁ → Γ₀

-- Contexts are presheaves over { 0 → 1 }

F : Con → Con''''
F (Γ₀ , Γ₁) = (Γ₀ , Σ Γ₀ Γ₁ , λ (γ₀ , _) → γ₀)

G : Con'''' → Con
G (Γ₀ , Γ₁ , f) = (Γ₀ , λ γ₀ → Σ Γ₁ (λ γ₁ → γ₀ ≡ f γ₁))

-- Presheaf model
-- Parameters:
postulate
  Ob : Set
  Hom : Ob → Ob → Set

record ConPsh : Set₁ where
  field Γ : Ob → Set
        restrict : ∀ {x y} → Hom y x → (Γ x) → (Γ y)
        -- + some equalities
