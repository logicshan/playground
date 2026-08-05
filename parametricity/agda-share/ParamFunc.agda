
module ParamFunc where

open import LFT

open import Function

open import Data.Product

open import Relation.Binary.PropositionalEquality

record IsFunctor (F : Set → Set) (map : ∀{A B} → (A → B) → (F A → F B))
    : Set₁ where
  field
    map-id : ∀{A : Set} → map id ≡ id {A = F A}
    map-∘  : ∀{A B C : Set} (f : A → B) (g : B → C)
           → map (g ∘ f) ≡ map g ∘ map f

Id : Set → Set
Id T = T

map-Id : ∀{A B} → (A → B) → Id A → Id B
map-Id f = f

id-func : IsFunctor Id map-Id
id-func = record { map-id = refl
                 ; map-∘  = λ f g → refl
                 }

postulate
  ext : ∀{A : Set} {B : A → Set} → (f g : (x : A) → B x)
      → (∀ x → f x ≡ g x) → f ≡ g

module M (A B : Set) where
  Mapped : Set₁
  Mapped = (F : Set → Set) → F A → F B

  [Mapped] : _
  [Mapped] = [Π] ([Set] [→] [Set]) \F → F {A} _≡_ [→] F {B} _≡_

  postulate
    param-Mapped : ∀(T : Mapped) → [Mapped] T T

  lemma₁ : ∀{T : Set} → (f : T → T) → (∀ x → x ≡ f x) → f ≡ id {_} {T}
  lemma₁ f = sym ∘ ext id f

  lemma₂ : ∀{T : Set} → (f : T → T) → (∀ x → x ≡ f x)
         → {F₁ F₂ : Set → Set} → {map₁ : ∀{X Y} → (X → Y) → F₁ X → F₁ Y}
         → IsFunctor F₁ map₁
         → (η : ∀ X → F₁ X → F₂ X)
         → ∀ x → η T (map₁ f x) ≡ η T x
  lemma₂ {T} f pf {map₁ = map} Fun η x
      = begin
          η T (map f x)
        ≡⟨ cong (λ g → η T (map g x)) (lemma₁ f pf) ⟩
          η T (map id x)
        ≡⟨ cong (λ g → η T (g x)) (IsFunctor.map-id Fun) ⟩
          η T x
        ∎
    where
    open ≡-Reasoning

  pre-free : (y : Mapped)
           → (F₁ F₂ : Set → Set)
           → (map₁ : ∀{A B} → (A → B) → F₁ A → F₁ B)
           → (map₂ : ∀{A B} → (A → B) → F₂ A → F₂ B)
           → IsFunctor F₁ map₁
           → IsFunctor F₂ map₂
           → (η : ∀ A → F₁ A → F₂ A)
           → ∀ x → η B (map₁ id (y F₁ x)) ≡ y F₂ (η A x)
  pre-free y F₁ F₂ map₁ map₂ Fun₁ Fun₂ η x
    = param-Mapped y {F₁} {F₂}
        (λ{X} {Y} _~_ F₁X F₂Y → ∀(f : X → Y)
                              → (∀ x → x ~ f x) → η Y (map₁ f F₁X) ≡ F₂Y)
        {x} {η A x} (λ f pf → lemma₂ f pf Fun₁ η x) id (λ _ → refl)

  free : (y : Mapped)
       → (F₁ F₂ : Set → Set)
       → (map₁ : ∀{A B} → (A → B) → F₁ A → F₁ B)
       → (map₂ : ∀{A B} → (A → B) → F₂ A → F₂ B)
       → IsFunctor F₁ map₁
       → IsFunctor F₂ map₂
       → (η : ∀ A → F₁ A → F₂ A)
       → ∀ x → η B (y F₁ x) ≡ y F₂ (η A x)
  free y F₁ F₂ map₁ map₂ Fun₁ Fun₂ η x
    = subst (λ g → η B (g (y F₁ x)) ≡ y F₂ (η A x))
            (IsFunctor.map-id Fun₁) (pre-free y F₁ F₂ map₁ map₂ Fun₁ Fun₂ η x)
  