
module PW where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data U : Set
T : U → Set

data U where
  ø ∙ : U
  σ π : (a : U) → (b : T a → U) → U

T ø       = ⊥
T ∙       = ⊤
T (σ a b) = Σ (T a) (λ x → T (b x))
T (π a b) = (x : T a) → T (b x)

w : (a : U) → (b : T a → U) → U
w a b = σ a (λ x → π (b x) (λ _ → ø))

postulate
  ext : {A : Set} {B : A → Set} → (f g : (x : A) → B x) → (∀ x → f x ≡ g x) → f ≡ g

U-prop : (u : U) → (x y : T u) → x ≡ y
U-prop ø       ()       ()
U-prop ∙       x        y       = refl
U-prop (π a b) f        g = ext f g $ λ x → U-prop (b x) (f x) (g x)
U-prop (σ a b) (w , x) (y  ,  z) with U-prop a w y
U-prop (σ a b) (w , x) (.w ,  z) | refl with U-prop (b w) x z
U-prop (σ a b) (w , x) (.w , .x) | refl | refl = refl

tree : (a : U) (b : T a → U) → (x : T a) → (y : T (b x) → T (w a b)) → T (w a b)
tree a b x y = x , λ z →
  let w = y z
   in subst (λ e → ¬ T (b e)) (U-prop a (proj₁ w) x) (proj₂ w) z

w-rec : (a : U) (b : T a → U) (r : U)
      → ((x : T a) → (y : T (b x) → T r) → T r) → T (w a b) → T r
w-rec u b r f (x , ¬b) = f x (⊥-elim ∘ ¬b)

w-ind : (a : U) (b : T a → U) (r : T (w a b) → U)
      → ((x : T a) → (y : T (b x) → Σ (T (w a b)) (T ∘ r)) → T (r (tree a b x (proj₁ ∘ y))))
      → (e : T (w a b)) → T (r e)
w-ind a b r f (x , ¬b) = subst (λ e → T (r e)) (U-prop (w a b) _ _) $ f x $ λ z → ⊥-elim $ ¬b z
