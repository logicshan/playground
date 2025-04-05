
module HM where

open import Meta

infixr 30 _⇒_
infixr 40 _⊕_
infixr 50 _⊗_
data M : Set where
  ∅   : M
  ●   : M
  _⊕_ : M → M → M
  _⊗_ : M → M → M
  _⇒_ : M → M → M

infix 20 ,_
data P : Set where
  Π  : (M → P) → P
  ,_ : M → P

TM : M → Set
TM ∅ = ⊥
TM ● = ⊤
TM (a ⊕ b) = TM a ⊎ TM b
TM (a ⊗ b) = TM a × TM b
TM (a ⇒ b) = TM a → TM b

TP : P → Set
TP (Π e) = ∀(s : M) → TP (e s)
TP (, m) = TM m

id : TP (Π \a → , a ⇒ a)
id A x = x

const : TP (Π \a → Π \b → , a ⇒ b ⇒ a)
const A B x y = x

data TermM : M → Set where
  _!_ : ∀ a → TermM ∅ → TermM a
  un  : TermM ●
  v   : ∀{a}     → TM a → TermM a
  l   : ∀{a b}   → TermM a → TermM (a ⊕ b)
  r   : ∀{a b}   → TermM b → TermM (a ⊕ b)
  c   : ∀{a b r} → (TermM (a ⇒ r)) → (TermM (b ⇒ r)) → TermM (a ⊕ b) → TermM r
  _&_ : ∀{a b}   → TermM a → TermM b → TermM (a ⊗ b)
  f   : ∀{a b}   → TermM (a ⊗ b) → TermM a
  s   : ∀{a b}   → TermM (a ⊗ b) → TermM b
  lam : ∀{a b}   → (TM a → TermM b) → TermM (a ⇒ b)
  _∙_ : ∀{a b}   → (TermM (a ⇒ b)) → TermM a → TermM b

infix 10 Λ_
infix 20 ^_
data TermP : P → Set where
  Λ_ : ∀{t} → (∀{a} → TermP (t a)) → TermP (Π t)
  ^_ : ∀{a} → TermM a → TermP (, a)

id₂ : TermP (Π \a → , a ⇒ a)
id₂ = Λ ^ lam \x → v x

const₂ : TermP (Π \a → Π \b → , a ⇒ b ⇒ a)
const₂ = Λ Λ ^ lam \x → lam \y → v x

-- unresolved metas
-- curry : TermP (Π \a → Π \b → Π \c → , (a ⊗ b ⇒ c) ⇒ a ⇒ b ⇒ c)
-- curry = Λ Λ Λ ^ lam \f → lam \x → lam \y → v f ∙ (v x & v y)