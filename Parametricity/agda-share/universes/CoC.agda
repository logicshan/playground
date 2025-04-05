
module CoC where

mutual
  data U₀ : Set where
    Π₀ : (s : U₀) (f : T₀ s → U₀) → U₀

  T₀ : U₀ → Set
  T₀ (Π₀ s f) = (x : T₀ s) → T₀ (f x)

  data U₁ : Set where
    Πω : (s : U₁) (f : T₁ s → U₁) → U₁
    Π₁ : (s : U₀) (f : T₀ s → U₁) → U₁
    Π₂ : (s : U₁) (f : T₁ s → U₀) → U₁
    ∗  : U₁

  T₁ : U₁ → Set
  T₁ (Πω s f) = (x : T₁ s) → T₁ (f x)
  T₁ (Π₁ s f) = (x : T₀ s) → T₁ (f x)
  T₁ (Π₂ s f) = (x : T₁ s) → T₀ (f x)
  T₁ ∗        = U₀

data Sort : Set where
  set  : Sort
  type : Sort

_⊔_ : Sort → Sort → Sort
set ⊔ set = set
_   ⊔ _   = type

[_] : Sort → Set
[ set ]  = U₀
[ type ] = U₁

⟦_⟧ : ∀{s : Sort} → [ s ] → Set
⟦_⟧ {set}  t = T₀ t
⟦_⟧ {type} t = T₁ t

Π : ∀{s₁ s₂ : Sort} → (a : [ s₁ ]) → (f : ⟦ a ⟧ → [ s₂ ]) → [ s₁ ⊔ s₂ ]
Π {set}  {set}  = Π₀
Π {set}  {type} = Π₁
Π {type} {set}  = Π₂
Π {type} {type} = Πω

infixr 0 _⇒_
_⇒_ : ∀{s₁ s₂ : Sort} → (a : [ s₁ ]) (b : [ s₂ ]) → [ s₁ ⊔ s₂ ]
a ⇒ b = Π a (\_ → b)

id : ⟦ Π ∗ (\a → a ⇒ a) ⟧
id a x = x

const : ⟦ (Π ∗ \a → Π ∗ \b → a ⇒ b ⇒ a) ⟧
const a b x y = x

module Unrestricted where

  -- not typeable internally
  Eq : (a : [ set ]) → (x y : ⟦ a ⟧) → [ type ]
  Eq a x y = Π (a ⇒ ∗) \p → p x ⇒ p y

  mutual
    data Tm : {s : Sort} → [ s ] → Set where
      lit : ∀{s}     {a : [ s ]} → ⟦ a ⟧ → Tm a
      lam : ∀{s₁ s₂} (a : [ s₁ ]) {f : ⟦ a ⟧ → [ s₂ ]}
          → ((x : ⟦ a ⟧) → Tm (f x)) → Tm (Π a f)
      _∙_ : ∀{s₁ s₂} {a : [ s₁ ]} {f : ⟦ a ⟧ → [ s₂ ]}
          → (g : Tm (Π a f)) (x : Tm a) → Tm (f (eval x))
      pi  : ∀(a : [ set ]) (f : ⟦ a ⟧ → [ set ]) → Tm ∗

    eval : ∀{s : Sort} {a : [ s ]} → Tm a → ⟦ a ⟧
    eval (lit x)                 = x
    eval (lam {set}  {set}  _ e) = \x → eval (e x)
    eval (lam {type} {set}  _ e) = \x → eval (e x)
    eval (lam {set}  {type} _ e) = \x → eval (e x)
    eval (lam {type} {type} _ e) = \x → eval (e x)
    eval (_∙_ {set}  {set}  f x) = eval f (eval x)
    eval (_∙_ {type} {set}  f x) = eval f (eval x)
    eval (_∙_ {set}  {type} f x) = eval f (eval x)
    eval (_∙_ {type} {type} f x) = eval f (eval x)
    eval (pi a f)                = Π a f

  refl : Tm (Π ∗ \a → Π a \x → Eq a x x)
  refl = lam ∗ (\a → lam a \x → lam (a ⇒ ∗) \p → lam (p x) \px → lit px)

  id₂ : Tm (Π ∗ \a → a ⇒ a)
  id₂ = lam ∗ \a → lam a \x → lit x