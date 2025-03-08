module Deep where

-- The λ-calculus simple types
infixr 7 _⇒_
data type : Set where
  nat : type
  _⇒_ : type → type → type

-- The λ-calculus typing context, we use de Bruijn indices
infixl 5 _⨟_
data context : Set where
  ∙ : context
  _⨟_ : context → type → context

-- A ∈ Γ is the type of those de Bruijn indices whose type in Γ is A
infix 3 _∈_
data _∈_ : type → context → Set where
  z : ∀ {A : type} {Γ : context} → A ∈ Γ ⨟ A
  s : ∀ {A B : type} {Γ : context} → B ∈ Γ → B ∈ Γ ⨟ A

-- term Γ A is the type of λ-calculus terms of type A in context Γ
data term : context → type → Set where
  zero : ∀ {Γ} → term Γ nat
  succ : ∀ {Γ} → term Γ nat → term Γ nat
  var : ∀ {Γ A} → A ∈ Γ → term Γ A
  lam : ∀ {Γ} A {B} → term (Γ ⨟ A) B → term Γ (A ⇒ B)
  app : ∀ {Γ A B} → term Γ (A ⇒ B) → term Γ A → term Γ B

-- The λ-calculus typing judgement x : nat ⨟ f : nat ⇒ nat⨟ y : nat ⊢ succ (succ x) : nat
example-1 : term (∙ ⨟ nat ⨟ nat ⇒ nat ⨟ nat) nat
example-1 = succ (succ (var (s (s z))))

-- The λ-calculus typing judgement ∙ ⊢ (λ (x y : nat) succ x) (succ (succ 0)) : nat ⇒ nat
example-2 : term ∙ (nat ⇒ nat)
example-2 = app (lam nat (lam nat (succ (var (s z))))) (succ (succ zero) )

-- The λ-calculus typing judgement f : A ⇒ A ⊢ λ (x : A) f (f x) : A ⇒ A
example-3 : {A : type} → term (∙ ⨟ A ⇒ A) (A ⇒ A)
example-3 {A} = lam A (app (var (s z)) (app (var (s z)) (var z)))
