
module DepCat where

open import Function

open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

! : ∀{I} → I → ⊤
! _ = tt

-- In category theory, Martin-löf type theory is typically presented
-- in terms of locally cartesian closed categories. This is a category
-- C for which all slice categories C/A are cartesian closed. Here,
-- our category will be Set.
--
-- In that presentation, families of types indexed by I are taken to
-- be objects in C/I. Then, if f : A → I corresponds to the family
-- F : I → Set, F i = f⁻¹ i. However, it will be easier in Agda to
-- have an equivalent category of families in the usual Agda sense.

Fam : (I : Set) → Set₁
Fam I = I → Set

infix 20 _⇒_
_⇒_ : {I : Set} → Fam I → Fam I → Set
F ⇒ G = ∀{i} → F i → G i

-- Still, we expect Fam I to be cartesian closed for every I

1̂ : ∀{I} → Fam I
1̂ = λ _ → ⊤

!̂ : ∀{I} (F : Fam I) → F ⇒ 1̂
!̂ F = λ _ → tt

infix 60 _×̂_
_×̂_ : ∀{I} (F G : Fam I) → Fam I
F ×̂ G = λ i → F i × G i

π̂₁ : ∀{I} {F G : Fam I} → F ×̂ G ⇒ F
π̂₁ = proj₁

π̂₂ : ∀{I} {F G : Fam I} → F ×̂ G ⇒ G
π̂₂ = proj₂

infix 70 _^̂_
_^̂_ : ∀{I} (G F : Fam I) → Fam I
G ^̂ F = λ i → F i → G i

eval : ∀{I} {G F : Fam I} → G ^̂ F ×̂ F ⇒ G
eval (f , x) = f x

cur̂ry : ∀{I} {F G H : Fam I} → (H ×̂ F ⇒ G) → H ⇒ G ^̂ F
cur̂ry f = λ x y → f (x , y)

-- Moreover, our base category is isomorphic to the slice over/families
-- indexed by the terminal object.

Lift : Set → Fam ⊤
Lift B = λ _ → B

lift-→ : ∀{A B : Set} → (A → B) → Lift A ⇒ Lift B
lift-→ f = f

Lower : Fam ⊤ → Set
Lower F = F _

lower-⇒ : ∀{F G : Fam ⊤} → (F ⇒ G) → Lower F → Lower G
lower-⇒ f = f

-- Next, one considers a "change of index" functor. Any function
-- f : J → I in the base category induces a functor f⋆ : C/I → C/J.
-- In the standard categorical presentation, this is via pullback,
-- but with Agda-like families, it's just composition:

infix 40 _⋆
_⋆ : ∀{I J} → (J → I) → Fam I → Fam J
f ⋆ = λ F → F ∘ f

-- Dependent sums and products are left and right adjoints to this functor,
-- respectively.

Σ̂ : ∀{I J} → (I → J) → Fam I → Fam J
Σ̂ f F = λ j → Σ _ (λ i → f i ≡ j × F i)

Π̂ : ∀{I J} → (I → J) → Fam I → Fam J
Π̂ f F = λ j → ∀ i → f i ≡ j → F i

adj-Σ₁ : ∀{I J} {f : I → J} {F G} → (Σ̂ f F ⇒ G) → (F ⇒ (f ⋆) G)
adj-Σ₁ h x = h (_ , refl , x)

adj-Σ₂ : ∀{I J} {f : I → J} {F G} → (F ⇒ (f ⋆) G) → (Σ̂ f F ⇒ G)
adj-Σ₂ h (i , refl , x) = h x

adj-Π₁ : ∀{I J} {f : I → J} {F G} → ((f ⋆) F ⇒ G) → (F ⇒ Π̂ f G)
adj-Π₁ {F = F} h {j} x = λ i eq → h (subst F (sym eq) x)

adj-Π₂ : ∀{I J} {f : I → J} {F G} → (F ⇒ Π̂ f G) → ((f ⋆) F ⇒ G)
adj-Π₂ h x = h x _ refl

-- The dependent constructs enter into the base category via the terminal
-- slice.
--
--   Σ I F = Lower (Σ̂ ! F)
--   Π I F = Lower (Π̂ ! F)

∑ : (I : Set) (F : Fam I) → Set
∑ I F = Lower (Σ̂ ! F)

∏ : (I : Set) (F : Fam I) → Set
∏ I F = Lower (Π̂ ! F)

iso-Σ₁ : ∀{I F} → ∑ I F → Σ I F
iso-Σ₁ (i , refl , x) = (i , x)

iso-Σ₂ : ∀{I F} → Σ I F → ∑ I F
iso-Σ₂ (i , x) = (i , refl , x)

iso-Π₁ : ∀{I F} → ∏ I F → ((i : I) → F i)
iso-Π₁ f i = f i refl

iso-Π₂ : ∀{I F} → ((i : I) → F i) → ∏ I F
iso-Π₂ f i refl = f i

--
-- And since Lift and Lower are inverse, we also have:
--
--   Lift (Σ I F) = Σ̂ ! F
--   Lift (Π I F) = Π̂ ! F
--
-- Now we consider Σ I F → R.

trans₁ : ∀{I R : Set} {F : Fam I} → (Lower (Σ̂ ! F) → R) → (Σ̂ ! F ⇒ Lift R)
trans₁ = lift-→

trans₂ : ∀{I R : Set} {F : Fam I} → (Σ̂ ! F ⇒ Lift R) → (F ⇒ (! ⋆) (Lift R))
trans₂ = adj-Σ₁

-- So a function Σ I F → R is equivalent to a family morphism
-- F ⇒ ! ⋆ Lift R. This is in turn equivalent to a family morphism
-- 1̂ ×̂ F ⇒ ! ⋆ Lift R.

trans₃ : ∀{I R : Set} {F : Fam I}
       → (F ⇒ (! ⋆) (Lift R)) → (1̂ ×̂ F ⇒ (! ⋆) (Lift R))
trans₃ {I} {R} {F} f {i} = f ∘ π̂₂ {I} {1̂} {F} {i}

-- But, Fam I is cartesian closed, so we can curry this.

trans₄ : ∀{I R : Set} {F : Fam I}
       → (1̂ ×̂ F ⇒ (! ⋆) (Lift R))
       → (1̂ ⇒ (! ⋆) (Lift R) ^̂ F)
trans₄ = cur̂ry

-- Now, this is 1̂ : Fam I, but note that that is equal to
-- (! ⋆) (1̂ : Fam ⊤)

trans₅ : ∀{I R : Set} {F : Fam I}
       → (1̂ ⇒ (! ⋆) (Lift R) ^̂ F)
       → ((! ⋆) 1̂ ⇒ (! ⋆) (Lift R) ^̂ F)
trans₅ f = f

-- And this fits the form of the adjunction for Π

trans₆ : ∀{I R : Set} {F : Fam I}
       → ((! ⋆) 1̂ ⇒ (! ⋆) (Lift R) ^̂ F)
       → (1̂ ⇒ Π̂ ! ((! ⋆) (Lift R) ^̂ F))
trans₆ = adj-Π₁

-- This is a morphism in Fam ⊤, so we can lower it.
trans₇ : ∀{I R : Set} {F : Fam I}
       → (1̂ ⇒ Π̂ ! ((! ⋆) (Lift R) ^̂ F))
       → ⊤ → Lower (Π̂ ! ((! ⋆) (Lift R) ^̂ F))
trans₇ = lower-⇒

trans₈ : ∀{I R : Set} {F : Fam I}
       → (⊤ → ∏ I ((! ⋆) (Lift R) ^̂ F))
       → ⊤ → (∀ i → F i → R)
trans₈ f = iso-Π₁ ∘ f

-- And it turns out this all simplifies to:
K : ∀{I : Set} → Set → Fam I
K R = (! ⋆) (Lift R)

dependent-curry' : ∀{I R : Set} {F : Fam I}
                 → (∑ I F → R) → (⊤ → ∏ I (K R ^̂ F))
dependent-curry' = trans₇ ∘ trans₆ ∘ trans₅ ∘ trans₄ ∘ trans₃ ∘ trans₂ ∘ trans₁

dependent-curry : ∀{I R : Set} {F : Fam I}
                → (Σ I F → R) → ⊤ → (∀ i → F i → R)
dependent-curry f = trans₈ ∘ dependent-curry' $ f ∘ iso-Σ₁

