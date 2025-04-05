
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Function

module Two (M : Set)
           (_∈_ : M → M → Set)
           (P : M → M)
           (def₁ : ∀{x y} → (∀ z → z ∈ y → z ∈ x) → y ∈ P x)
           (def₂ : ∀{x y} → y ∈ P x → (∀ z → z ∈ y → z ∈ x))
           (∅ ⦃∅⦄ : M)
           (def₃ : ∀ z → ¬ z ∈ ∅)
           (def₄ : ∅ ∈ ⦃∅⦄)
           (def₅ : ∀ z → z ∈ ⦃∅⦄ → z ≡ ∅)
           (ext : ∀{x y} → (∀ z → z ∈ x → z ∈ y) → (∀ z → z ∈ y → z ∈ x) → x ≡ y)
  where

_⊆_ : M → M → Set
x ⊆ y = ∀ z → z ∈ x → z ∈ y

_∧_ : Set → Set → Set
_∧_ = _×_
infixr 0 _∧_

_∨_ : Set → Set → Set
_∨_ = _⊎_
infixr 1 _∨_

Empty : M → Set
Empty X = ∀ z → ¬ z ∈ X

NonEmpty : M → Set
NonEmpty X = ¬ (∀ z → ¬ z ∈ X)

AtLeastTwo : M → Set
AtLeastTwo X = ∃ \a → ∃ \b → a ∈ X ∧ b ∈ X ∧ a ≢ b

Two : M → Set
Two X = ∃ \a → ∃ \b → a ∈ X ∧ b ∈ X ∧ a ≢ b ∧ (∀ c → a ≡ c ∨ b ≡ c)

AtMostTwo : M → Set
AtMostTwo X = ∀ a b c → a ∈ X → b ∈ X → c ∈ X → a ≡ b ∨ a ≡ c ∨ b ≡ c

WeaklyTwo : M → Set
WeaklyTwo X = ∃ \a → ∃ \b → a ∈ X ∧ b ∈ X ∧ a ≢ b ∧ (∀ c → c ∈ X → a ≢ c → b ≢ c → ⊥)

WeaklyAtMostTwo : M → Set
WeaklyAtMostTwo X = ∀ x y z → x ∈ X → y ∈ X → z ∈ X → x ≢ y → y ≢ z → x ≢ z → ⊥

empty! : ∀ E {X} → Empty E → E ⊆ X
empty! E em z z∈∅ = ⊥-elim $ em z z∈∅

∅∈P1 : ∅ ∈ P ⦃∅⦄
∅∈P1 = def₁ $ empty! ∅ def₃

⊆-refl : ∀ x → x ⊆ x
⊆-refl x z z∈x = z∈x

1∈P1 : ⦃∅⦄ ∈ P ⦃∅⦄
1∈P1 = def₁ $ ⊆-refl ⦃∅⦄

∅≢1 : ∅ ≢ ⦃∅⦄
∅≢1 eq = def₃ ∅ $ subst (_∈_ ∅) (sym eq) def₄

at-least-two : AtLeastTwo (P ⦃∅⦄)
at-least-two = ∅ , ⦃∅⦄ , ∅∈P1 , 1∈P1 , ∅≢1

lemma : ∀ c → c ∈ P ⦃∅⦄ → ∅ ≢ c → ⦃∅⦄ ≢ c → ⊥
lemma c c∈P1 ∅≢c ⦃∅⦄≢c = sub-lemma₁ sub-lemma₂
 where
 c⊆⦃∅⦄ : c ⊆ ⦃∅⦄
 c⊆⦃∅⦄ = def₂ c∈P1

 sub-lemma₀ : ∀ z → z ∈ c → z ≡ ∅
 sub-lemma₀ z z∈c = def₅ z (c⊆⦃∅⦄ z z∈c)

 sub-lemma₁ : NonEmpty c
 sub-lemma₁ em = ∅≢c $ ext (empty! ∅ def₃) (empty! c em)

 sub-lemma₂ : Empty c
 sub-lemma₂ z z∈c = ⦃∅⦄≢c $
   ext (λ z' z'∈⦃∅⦄ → subst (λ w → w ∈ c) (sym (def₅ z' z'∈⦃∅⦄)) ∅∈c)
       c⊆⦃∅⦄
  where
  ∅∈c : ∅ ∈ c
  ∅∈c = subst (λ w → w ∈ c) (sub-lemma₀ z z∈c) z∈c

weakly-two : WeaklyTwo (P ⦃∅⦄)
weakly-two = ∅ , ⦃∅⦄ , ∅∈P1 , 1∈P1 , ∅≢1 , lemma

tr : ∀{A : Set} {x y z : A} → x ≡ y → x ≡ z → y ≡ z
tr xy xz = trans (sym xy) xz

wt⇒wamt : ∀ X → WeaklyTwo X → WeaklyAtMostTwo X
wt⇒wamt X (a , b , a∈X , b∈X , a≢b , ¬c) x y z x∈X y∈X z∈X x≢y y≢z x≢z =
  ¬c x x∈X
    (λ a≡x → ¬c y y∈X
               (λ a≡y → x≢y $ tr a≡x a≡y)
               (λ b≡y → ¬c z z∈X
                          (λ a≡z → x≢z $ tr a≡x a≡z)
                          (λ b≡z → y≢z $ tr b≡y b≡z)))
    (λ b≡x → ¬c y y∈X
               (λ a≡y → ¬c z z∈X
                          (λ a≡z → y≢z $ tr a≡y a≡z)
                          (λ b≡z → x≢z $ tr b≡x b≡z))
               (λ b≡y → x≢y $ tr b≡x b≡y))

t⇒amt : ∀ X → Two X → AtMostTwo X
t⇒amt X (a , b , a∈X , b∈X , a≢b , eq) x y z x∈X y∈X z∈X with eq x | eq y | eq z
... | inj₁ ax | inj₁ ay | _       = inj₁        $ tr ax ay
... | inj₁ ax | _       | inj₁ az = inj₂ $ inj₁ $ tr ax az
... | inj₂ bx | inj₂ by | _       = inj₁        $ tr bx by
... | inj₂ bx | _       | inj₂ bz = inj₂ $ inj₁ $ tr bx bz
... | _       | inj₁ ay | inj₁ az = inj₂ $ inj₂ $ tr ay az
... | _       | inj₂ by | inj₂ bz = inj₂ $ inj₂ $ tr by bz


module Two? (Comp : M → (M → Set) → M)
            (def₆ : ∀{X p} z → z ∈ Comp X p → z ∈ X ∧ p z)
            (def₇ : ∀{X p} z → z ∈ X → p z → z ∈ Comp X p)
            (hyp : AtMostTwo (P ⦃∅⦄))
            (A : Set)
  where
  C = Comp ⦃∅⦄ (const A)

  C∈P1 : C ∈ P ⦃∅⦄
  C∈P1 = def₁ $ λ z → proj₁ ∘ def₆ z


  lem : A ∨ ¬ A
  lem with hyp ∅ ⦃∅⦄ C ∅∈P1 1∈P1 C∈P1
  ... | inj₁ ∅≡1 = ⊥-elim (∅≢1 ∅≡1)
  ... | inj₂ (inj₁ ∅≡C) = inj₂ $ λ a → def₃ ∅ $ subst (_∈_ ∅) (sym ∅≡C) $ def₇ ∅ def₄ a
  ... | inj₂ (inj₂ 1≡C) = inj₁ $ proj₂ $ def₆ ∅ $ subst (_∈_ ∅) 1≡C def₄
