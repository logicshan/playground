
module Bindings where

data Ty : Set where
  _⇒_ : (t u : Ty) → Ty

data Var (b : Ty) (A : Ty → Set) : Ty → Set where
  top : Var b A b
  pop : ∀{t} → A t → Var b A t

_⇉_ : (A B : Ty → Set) → Set
A ⇉ B = ∀ t → A t → B t

module V where
  pure : ∀{b} {A : Ty → Set} → A ⇉ Var b A 
  pure _ = pop

  map : ∀{b} {A B} → (A ⇉ B) → Var b A ⇉ Var b B
  map f t top     = top
  map f t (pop x) = pop (f t x)

  bind : ∀{b} {A B : Ty → Set} → (A ⇉ Var b B) → Var b A ⇉ Var b B
  bind f t top     = top
  bind f t (pop x) = f t x

module Plain where
  data Exp (A : Ty → Set) : Ty → Set where
    _∙_ : ∀{t u} → Exp A (t ⇒ u) → Exp A t → Exp A u
    var : ∀{t} → A t → Exp A t
    lam : ∀{t u} → Exp (Var t A) u → Exp A (t ⇒ u)

  pure : ∀{A} → A ⇉ Exp A
  pure _ = var

  map : ∀{A B} → (A ⇉ B) → Exp A ⇉ Exp B
  map f t        (var x)         = var (f t x)
  map f t        (g ∙ x)         = map f _ g ∙ map f _ x
  map f .(t ⇒ u) (lam {t} {u} e) = lam (map (V.map f) _ e)

  trav : ∀{A B : Ty → Set} {t} → (A ⇉ Exp B) → Var t A ⇉ Exp (Var t B)
  trav f t top     = pure _ top
  trav f u (pop x) = map (λ _ → pop) _ (f _ x)

  bind : ∀{A B : Ty → Set} → (A ⇉ Exp B) → Exp A ⇉ Exp B
  bind f t        (var x)         = f t x
  bind f t        (g ∙ x)         = bind f _ g ∙ bind f _ x
  bind f .(t ⇒ u) (lam {t} {u} x) = lam (bind (trav f) _ x)

module Generalized where
  data Exp (A : Ty → Set) : Ty → Set where
    var : ∀{t} → A t → Exp A t
    _∙_ : ∀{t u} → (f : Exp A (t ⇒ u)) → (x : Exp A t) → Exp A u
    lam : ∀{t u} → (e : Exp (Var t (Exp A)) u) → Exp A (t ⇒ u)

  pure : ∀{A} → A ⇉ Exp A
  pure _ = var

  map : ∀{A B} → (A ⇉ B) → Exp A ⇉ Exp B
  {-# NO_TERMINATION_CHECK #-}
  map f t        (var x)         = var (f t x)
  map f t        (g ∙ x)         = map f _ g ∙ map f _ x
  map f .(t ⇒ u) (lam {t} {u} e) = lam (map (V.map (map f)) _ e)

  bind : ∀{A B} → (A ⇉ Exp B) → Exp A ⇉ Exp B
  {-# NO_TERMINATION_CHECK #-}
  bind f t        (var x)         = f t x
  bind f t        (g ∙ x)         = bind f _ g ∙ bind f _ x
  bind f .(t ⇒ u) (lam {t} {u} e) = lam (map (V.map (bind f)) _ e)
