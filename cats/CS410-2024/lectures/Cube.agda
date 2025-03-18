open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_) renaming (id to id')
open import Data.Sum hiding ([_,_])
open import Relation.Binary.PropositionalEquality
open import Category.Category
open import Data.Fin using (Fin; zero; suc)

module _ where

module _ where
  open Category

  FinSet : Category
  Obj FinSet = ℕ
  Hom FinSet n m = Fin n → Fin m
  id FinSet = id'
  comp FinSet f g = g ∘ f
  assoc FinSet = refl
  identityˡ FinSet = refl
  identityʳ FinSet = refl

module _ where
  open Category
  open Functor

  ⊎0,1 : Functor FinSet FinSet
  act ⊎0,1 I = suc (suc I)  -- if I = [0,1,2,...]
                            -- then ⊎0,1 I = 0,1,(map (suc∘suc) I)
  fmap ⊎0,1 f = λ{ zero → zero
                 ; (suc zero) → suc zero
                 ; (suc (suc x)) → suc (suc (f x)) }
  identity ⊎0,1 = ext (λ{ zero → refl ; (suc zero) → refl ; (suc (suc x)) → refl})
  homomorphism ⊎0,1 = ext λ{ zero → refl ; (suc zero) → refl ; (suc (suc x)) → refl }

module _ where
  open Category
  open Functor
  open NaturalTransformation
  open Monad

  ⊎0,1M : Monad FinSet
  functor ⊎0,1M = ⊎0,1
  transform (returnNT ⊎0,1M) I = λ i → suc (suc i)
  natural (returnNT ⊎0,1M) = λ _ _ _ → refl
  transform (joinNT ⊎0,1M) I =
    λ{ zero → zero
     ; (suc zero) → suc zero
     ; (suc (suc zero)) → zero
     ; (suc (suc (suc zero))) → suc zero
     ; (suc (suc (suc (suc i)))) → suc (suc i)}
  natural (joinNT ⊎0,1M) I J f = ext
    λ{ zero → refl
     ; (suc zero) → refl
     ; (suc (suc zero)) → refl
     ; (suc (suc (suc zero))) → refl
     ; (suc (suc (suc (suc i)))) → refl}
  returnJoin ⊎0,1M = ext
    λ{ zero → refl
     ; (suc zero) → refl
     ; (suc (suc zero)) → refl
     ; (suc (suc (suc zero))) → refl
     ; (suc (suc (suc (suc i)))) → refl }
  mapReturnJoin ⊎0,1M = ext
    λ{ zero → refl
     ; (suc zero) → refl
     ; (suc (suc zero)) → refl
     ; (suc (suc (suc zero))) → refl
     ; (suc (suc (suc (suc i)))) → refl }
  joinJoin ⊎0,1M = ext
    λ{ zero → refl
     ; (suc zero) → refl
     ; (suc (suc zero)) → refl
     ; (suc (suc (suc zero))) → refl
     ; (suc (suc (suc (suc zero)))) → refl
     ; (suc (suc (suc (suc (suc zero))))) → refl
     ; (suc (suc (suc (suc (suc (suc i)))))) → refl }

module _ where
  open import Category.Kleisli
  open Category

  KCubeᵒᵖ : Category
  KCubeᵒᵖ = Kleisli ⊎0,1M

  KCube : Category
  KCube = op KCubeᵒᵖ

  xᵒᵖ : Set
  xᵒᵖ = Hom KCubeᵒᵖ 2 1    -- Fin 2 → Fin 3

  x : Set
  x = Hom KCube 2 1       -- Fin 1 → Fin 4


module _ where

  [_,_] : {A B C : Set} → (f : A → C) → (g : B → C) → (A ⊎ B → C)
  [ f , g ] (inj₁ a) = f a
  [ f , g ] (inj₂ b) = g b

  open Category

  Cube : Category
  Obj Cube = ℕ
  Hom Cube I J = Fin J → Fin I ⊎ Fin 2       -- J → I⊔{0,1}
  id Cube = inj₁
  comp Cube f g = [ f , inj₂ ] ∘ g
  assoc Cube {A = I}{B = J}{C = K}{D = L} {f} {g} {h} = ext lemma
    where
    lemma₀ : (x : Fin K ⊎ Fin 2) → ([ f , inj₂ ] ∘ [ g , inj₂ ]) x ≡ ([ [ f , inj₂ ] ∘ g , inj₂ ]) x
    lemma₀ (inj₁ x) = refl
    lemma₀ (inj₂ y) = refl
    lemma : (x : Fin L) →
      [ f , inj₂ ] ([ g , inj₂ ] (h x)) ≡
      [ (λ x₁ → [ f , inj₂ ] (g x₁)) , inj₂ ] (h x)
    lemma x = lemma₀ (h x) 
  identityˡ Cube {B = J} {f = f} = ext lemma
    where
    lemma₀ : [ inj₁ , inj₂ ] ≡ id'
    lemma₀  = ext λ{ (inj₁ _) → refl ; (inj₂ _) → refl }
    lemma : (x : Fin J) → [ inj₁ , inj₂ ] (f x) ≡ f x
    lemma x = cong (λ 𝕗 → 𝕗 (f x)) lemma₀
  identityʳ Cube = refl
