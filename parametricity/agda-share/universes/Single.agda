
module Single where

import Meta
open Meta using ( _⊎_ ; _≡_ ; _$_ ; _∘_ ; _◂_ ; fst ; snd ; _,_
                ; Bool ; true ; false ; naughty ; if_then_else_ ; inl ; inr)

-- A single inductive recursive universe.

mutual
  data U : Set where
    ∅   : U
    ●   : U
    B   : U
    _⊕_ : (s t : U) → U
    Π   : (s : U) (f : T s → U) → U
    Σ   : (s : U) (f : T s → U) → U
    W   : (s : U) (f : T s → U) → U
    _≃_ : {s : U} (x y : T s) → U

  T : U → Set
  T ∅       = Meta.⊥
  T ●       = Meta.⊤
  T B       = Meta.Bool
  T (s ⊕ t) = T s ⊎ T t
  T (Π s f) = (S : T s) → T (f S)
  T (Σ s f) = Meta.Σ (T s) (λ S → T (f S))
  T (W s f) = Meta.W (T s) (λ S → T (f S))
  T (x ≃ y) = x ≡ y

-- _⇒_ : U → U → U
-- s ⇒ t = Π s (λ _ → t)

mutual
  infixl 90 _∙_
  data Term : U → Set where
    _!_   : ∀{s} → Type s → Term ∅ → Term s
    un    : Term ●
    tr fl : Term B
    cond  : ∀{p : Bool → U} (P : ∀ b → Type (p b)) (b : Term B)
          → Term (p true) → Term (p false) → Term (p ⟦ b ⟧)
    case  : ∀{s t} {p : T s ⊎ T t → U} (P : ∀ z → Type (p z))
                   (f : ∀ x → Term (p (inl x)))
                   (g : ∀ y → Term (p (inr y))) 
                     (z : Term (s ⊕ t)) → Term (p ⟦ z ⟧)
    val   : ∀{s} → T s → Term s
    lam   : ∀{s t} → (e : (x : T s) → Term (t x)) → Term (Π s t)
    _∙_   : ∀{s t} (f : Term (Π s t)) (x : Term s) → Term (t ⟦ x ⟧)
    ⟨_,_⟩ : ∀{s t} (x : Term s) (w : Term (t ⟦ x ⟧)) → Term (Σ s t)
    π₁    : ∀{s t} (p : Term (Σ s t)) → Term s
    π₂    : ∀{s t} (p : Term (Σ s t)) → Term (t $ fst ⟦ p ⟧)
    ι₁    : ∀{s t} → Type t → Term s → Term (s ⊕ t)
    ι₂    : ∀{s t} → Type s → Term t → Term (s ⊕ t)
    _◃_   : ∀{s t} (x : Term s) (f : T (t ⟦ x ⟧) → Term (W s t)) → Term (W s t)
    refl  : ∀{s} {x : Term s} → Term (⟦ x ⟧ ≃ ⟦ x ⟧)
    subst : ∀{s} (p : T s → U) {x y : Term s}
          → Term (⟦ x ⟧ ≃ ⟦ y ⟧) → Term (p ⟦ x ⟧) → Term (p ⟦ y ⟧)

  ⟦_⟧ : ∀{s} → Term s → T s
  ⟦ s ! n ⟧         = naughty ⟦ n ⟧
  ⟦ un ⟧            = _
  ⟦ tr ⟧            = true
  ⟦ fl ⟧            = false
  ⟦ cond _ b t f ⟧ with ⟦ b ⟧
  ... | true        = ⟦ t ⟧
  ... | false       = ⟦ f ⟧
  ⟦ case _ f g s ⟧ with ⟦ s ⟧
  ... | inl x       = ⟦ f x ⟧
  ... | inr y       = ⟦ g y ⟧
  ⟦ ι₁ _ x ⟧        = inl ⟦ x ⟧
  ⟦ ι₂ _ y ⟧        = inr ⟦ y ⟧
  ⟦ val y ⟧         = y
  ⟦ lam e ⟧         = λ x → ⟦ e x ⟧
  ⟦ f ∙ x ⟧         = ⟦ f ⟧ ⟦ x ⟧
  ⟦ ⟨ x , w ⟩ ⟧     = Meta._,_ ⟦ x ⟧ ⟦ w ⟧
  ⟦ π₁ p ⟧          = fst ⟦ p ⟧
  ⟦ π₂ p ⟧          = snd ⟦ p ⟧
  ⟦ x ◃ f ⟧         = ⟦ x ⟧ ◂ λ y → ⟦ f y ⟧
  ⟦ refl ⟧          = Meta.refl
  ⟦ subst p eq px ⟧ = Meta.subst (T ∘ p) ⟦ eq ⟧ ⟦ px ⟧

  -- well-formed (syntactic) types
  data Type : U → Set where
    ∅    : Type ∅
    ●    : Type ●
    B    : Type B
    _⊕_  : ∀{s t} → Type s → Type t → Type (s ⊕ t)
    Π    : ∀{s t} → Type s → (∀ x → Type (t x)) → Type (Π s t)
    Σ    : ∀{s t} → Type s → (∀ x → Type (t x)) → Type (Σ s t)
    W    : ∀{s t} → Type s → (∀ x → Type (t x)) → Type (W s t)
    I    : ∀{s}   → Type s → (x y : Term s) → Type (⟦ x ⟧ ≃ ⟦ y ⟧)
    Cond : ∀{s t} → (b : Term B) → Type s → Type t
         → Type (if ⟦ b ⟧ then s else t)

  [_] : ∀{s} → Type s → Set
  [_] {s} _ = Term s

_⇒_ : ∀{s t} → Type s → Type t → Type (Π s \_ → t)
S ⇒ T = Π S \_ → T

-- id : ∀{a} → Term (a ⇒ a)
id : ∀{s} {S : Type s} → [ S ⇒ S ]
id = lam \x → val x

{-
uncurry : ∀{a : U} {b : T a → U} {c : T (Σ a b) → U}
        → Term ((Π a \x → Π (b x) \y → c (x , y))
                              ⇒ (Π (Σ a b) \p → c p))
-}
uncurry : ∀{a : U} {b : T a → U} {c : T (Σ a b) → U}
           {A : Type a} {B : ∀ x → Type (b x)} {C : ∀ p → Type (c p)}
        → [ (Π A \x → Π (B x) \y → C (x , y)) ⇒ (Π (Σ A B) \p → C p) ]
uncurry = lam \f → lam \p → val f ∙ π₁(val p) ∙ π₂(val p)

{-
curry : ∀{a : U} {b : T a → U} {c : T (Σ a b) → U}
      → Term ((Π (Σ a b) \p → c p) ⇒ (Π a \x → Π (b x) \y → c (x , y)))
-}
curry : ∀{a : U} {b : T a → U} {c : T (Σ a b) → U}
         {A : Type a} {B : ∀ x → Type (b x)} {C : ∀ p → Type (c p)}
      → [ (Π (Σ A B) \p → C p) ⇒ (Π A \x → Π (B x) \y → C (x , y)) ]
curry = lam \f → lam \x → lam \y → val f ∙ ⟨ val x , val y ⟩
  