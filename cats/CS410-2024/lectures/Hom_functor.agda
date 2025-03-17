open import Relation.Binary.PropositionalEquality
open import Data.Product using (proj₁; proj₂; _,_) renaming (_×_ to _x_)
open import Category.Category

open Category

op : Category → Category
Obj (op C) = Obj C
Hom (op C) X Y = Hom C Y X
id (op C) = id C
comp (op C) f g = comp C g f
assoc (op C) {f = f} {g} {h} = sym (assoc C {f = h} {g} {f})
identityˡ (op C) = identityʳ C
identityʳ (op C) = identityˡ C

_×_ : Category → Category → Category
Obj (𝓒 × 𝓓) = Obj 𝓒 x Obj 𝓓
Hom (𝓒 × 𝓓) (s₁ , s₂) (t₁ , t₂) = Hom 𝓒 s₁ t₁ x Hom 𝓓 s₂ t₂
id (𝓒 × 𝓓) = id 𝓒 , id 𝓓
comp (𝓒 × 𝓓) (f₁ , g₁) (f₂ , g₂) = comp 𝓒 f₁ f₂ , comp 𝓓 g₁ g₂
assoc (𝓒 × 𝓓) = cong₂ _,_ (assoc 𝓒) (assoc 𝓓)
identityˡ (𝓒 × 𝓓) {A} {B} {f = f} = begin
  (comp 𝓒 (id 𝓒) (proj₁ f) , comp 𝓓 (id 𝓓) (proj₂ f))
    ≡⟨ cong₂ _,_ (identityˡ 𝓒) (identityˡ 𝓓) ⟩
  (proj₁ f , proj₂ f)
    ≡⟨⟩
  f ∎  where open ≡-Reasoning
identityʳ (𝓒 × 𝓓) {f = f} = begin
  (comp 𝓒 (proj₁ f) (id 𝓒) , comp 𝓓 (proj₂ f) (id 𝓓))
    ≡⟨ cong₂ _,_ (identityʳ 𝓒) (identityʳ 𝓓) ⟩
  (proj₁ f , proj₂ f)
    ≡⟨⟩
  f ∎ where open ≡-Reasoning

open Functor

Hom⟦-,-⟧ : (𝓒 : Category) → Functor ((op 𝓒) × 𝓒) SET
act (Hom⟦-,-⟧ 𝓒) (X , Y) = Hom 𝓒 X Y
fmap (Hom⟦-,-⟧ 𝓒) {X₁ , X₂} {Y₁ , Y₂} (f₁ , f₂)
  = λ g → comp 𝓒 f₁ (comp 𝓒 g f₂)
identity (Hom⟦-,-⟧ 𝓒) {X} = ext lemma
  where
  lemma : (f : Hom 𝓒 (proj₁ X) (proj₂ X))
          → comp 𝓒 (id 𝓒) (comp 𝓒 f (id 𝓒)) ≡ f
  lemma f = begin
    comp 𝓒 (id 𝓒) (comp 𝓒 f (id 𝓒))
      ≡⟨ cong (λ x → comp 𝓒 (id 𝓒) x) (identityʳ 𝓒) ⟩
    comp 𝓒 (id 𝓒) f
      ≡⟨ identityˡ 𝓒 ⟩
    f ∎ where open ≡-Reasoning
homomorphism (Hom⟦-,-⟧ 𝓒) {X₁ , X₂} {Y₁ , Y₂} {Z₁ , Z₂}
  {f₁ , f₂} {g₁ , g₂} = ext lemma
  where
  lemma : (h : Hom 𝓒 X₁ X₂) →
          comp 𝓒 (comp 𝓒 g₁ f₁) (comp 𝓒 h (comp 𝓒 f₂ g₂))
          ≡
          comp 𝓒 g₁ (comp 𝓒 (comp 𝓒 f₁ (comp 𝓒 h f₂)) g₂)
  lemma h = begin
    comp 𝓒 (comp 𝓒 g₁ f₁) (comp 𝓒 h (comp 𝓒 f₂ g₂))
      ≡⟨ assoc 𝓒 ⟨
    comp 𝓒 g₁ (comp 𝓒 f₁ (comp 𝓒 h (comp 𝓒 f₂ g₂)))
      ≡⟨ cong (λ 𝕗 → comp 𝓒 g₁ (comp 𝓒 f₁ 𝕗)) (assoc 𝓒) ⟩
    comp 𝓒 g₁ (comp 𝓒 f₁ (comp 𝓒 (comp 𝓒 h f₂) g₂))
      ≡⟨ cong (λ 𝕗 → comp 𝓒 g₁ 𝕗) (assoc 𝓒) ⟩
    comp 𝓒 g₁ (comp 𝓒 (comp 𝓒 f₁ (comp 𝓒 h f₂)) g₂) ∎
    where open ≡-Reasoning
