{-# OPTIONS --allow-unsolved-metas #-}
-- NOTE: I'm not yet content with this development; a cleanup is planned.
module Verona2024.Realizability.Common where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin hiding (raise)
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All hiding (toList)
open import Data.List.Membership.Propositional
open import Data.Vec hiding (length; toList)

infix 3 _↔_
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

data Ty : Set where
  * : Ty  -- just a single type for now, denoting the natural numbers

Cxt : Set
Cxt = List Ty

data Term (Γ : Cxt) : Ty → Set where
  Z   : Term Γ *
  S   : Term Γ * → Term Γ *
  var : {τ : Ty} → τ ∈ Γ → Term Γ τ

data Form (Γ : Cxt) : Set where
  ⊤ : Form Γ
  ⊥ : Form Γ
  _∧_ : Form Γ → Form Γ → Form Γ
  _∨_ : Form Γ → Form Γ → Form Γ
  _⇒_ : Form Γ → Form Γ → Form Γ
  FA  : {τ : Ty} → Form (τ ∷ Γ) → Form Γ
  EX  : {τ : Ty} → Form (τ ∷ Γ) → Form Γ
  _≈_ : {τ : Ty} → Term Γ τ → Term Γ τ → Form Γ

raise : {Γ : Cxt} {σ τ : Ty} → Term Γ τ → Term (σ ∷ Γ) τ
raise Z       = Z
raise (S t)   = S (raise t)
raise (var i) = var (there i)

Elems : {X : Set} → List X → Set
Elems xs = Σ[ x ∈ _ ] x ∈ xs

subs₀ : {Γ Δ : Cxt} {τ : Ty} → Term Γ τ → ({σ : Ty} → σ ∈ Γ → Term Δ σ) → Term Δ τ
subs₀ Z       f = Z
subs₀ (S t)   f = S (subs₀ t f)
subs₀ (var x) f = f x

subs : {Γ Δ : Cxt} → Form Γ → ({σ : Ty} → σ ∈ Γ → Term Δ σ) → Form Δ
subs ⊤       f = ⊤
subs ⊥       f = ⊥
subs (φ ∧ ψ) f = subs φ f ∧ subs ψ f
subs (φ ∨ ψ) f = subs φ f ∨ subs ψ f
subs (φ ⇒ ψ) f = subs φ f ⇒ subs ψ f
subs (FA φ)  f = FA (subs φ λ { (here p) → var (here p) ; (there i) → raise (f i) })
subs (EX φ)  f = FA (subs φ λ { (here p) → var (here p) ; (there i) → raise (f i) })
subs (s ≈ t) f = subs₀ s f ≈ subs₀ t f

record PCS : Set₁ where
  field
    Code  : Set
    _·_↓_ : Code → Code → Code → Set

module Aux (P… : PCS) where
  open PCS P…

  -- "f · x $ k" means: the computation f · x terminates, and any possible result validates k.
  _·_$_ : Code → Code → (Code → Set) → Set
  f · x $ k = (Σ[ y ∈ Code ] f · x ↓ y) × ((y : Code) → f · x ↓ y → k y)

  implies : (f x : Code) (k k' : Code → Set) (h : (y : Code) → k y → k' y) → f · x $ k → f · x $ k'
  implies f x k k' h ((y , fx↓y) , p) = (y , fx↓y) , (λ y q → h y (p y q))

  implies' : (f x : Code) (k : Code → Set) (k' : Set) (h : (y : Code) → k y → k') → f · x $ k → k'
  implies' f x k k' h ((y , fx↓y) , p) = h y (p y fx↓y)

  infixl 5 _·_
  data Expr (n : ℕ) : Set where
    _·_ : Expr n → Expr n → Expr n
    var : Fin n  → Expr n
    lit : Code   → Expr n

  _⟨_⟩ : {n : ℕ} → Expr (suc n) → Code → Expr n
  (f · x) ⟨ c ⟩ = (f ⟨ c ⟩) · (x ⟨ c ⟩)
  var zero    ⟨ c ⟩ = lit c
  var (suc i) ⟨ c ⟩ = var i
  lit e       ⟨ c ⟩ = lit e

  data _⇓_ {n : ℕ} : Expr n → Code → Set where
    triv : {x : Code} → lit x ⇓ x
    app
      : {f x : Expr n} {f' x' y : Code}
      → f ⇓ f'
      → x ⇓ x'
      → f' · x' ↓ y
      → (f · x) ⇓ y

  invert-triv : {n : ℕ} (x y : Code) → lit {n} x ⇓ y → y ≡ x
  invert-triv x .x triv = refl

  record IsPCA : Set where
    field
      lambda : {n : ℕ} → Expr (suc n) → Code

      lambda≥2-correct
        : {n : ℕ} {e : Expr (suc (suc n))} {x y : Code}
        → lambda e · x ↓ y
        → (y ≡ lambda (e ⟨ x ⟩))
      lambda1-correct
        : {e : Expr 1} {x y : Code}
        → (lambda e · x ↓ y ↔ (e ⟨ x ⟩) ⇓ y)

record PCA : Set₁ where
  field
    structure : PCS

  open PCS structure public
  open Aux structure public

  field
    isPCA : IsPCA

  open IsPCA isPCA public

module Church (P… : PCA) where
  open PCA P…

  pair : Code → Code → Code
  pair x y = lambda {0} (var zero · lit x · lit y)

  pair' : {n : ℕ} → Expr n → Expr n → Expr n
  pair' x y = lit (lambda {2} (var zero · var (suc (suc zero)) · var (suc zero))) · x · y

  -- For instance, the number 3 is represented as λzs.s(s(sz)).
  zer : Code
  zer = lambda {1} (var (suc zero))

  one : Code
  one = lambda {1} (var zero · var (suc zero))

  left : Code → Code
  left x = lambda {1} (var (suc zero) · lit x)

  right : Code → Code
  right y = lambda {1} (var zero · lit y)

  nat : ℕ → Code
  nat n = lambda {1} (go n)
    where
    go : ℕ → Expr 2
    go zero    = var (suc zero)
    go (suc n) = var zero · go n

  succ : Code → Code
  succ n = lambda {1} (var zero · (lit n · var (suc zero) · var zero))

  list : List Code → Code
  list []       = lambda {1} (var (suc zero))
  list (x ∷ xs) = lambda {1} (var zero · lit x · lit (list xs))

module Semantics (P… : PCA) where
  open PCA P…
  open Church P…

  Env : Cxt → Set
  Env Γ = {σ : Ty} → σ ∈ Γ → Code

  ∅ : Env []
  ∅ ()

  toList : {Γ : Cxt} → Env Γ → Vec Code (length Γ)
  toList {[]}    env = []
  toList {τ ∷ Γ} env = env (here refl) ∷ toList (λ i → env (there i))

  multi : {n : ℕ} → Expr n → Vec Code n → (Code → Set) → Set
  multi (f · x) xs k = multi f xs (λ f' → multi x xs (λ x' → f' · x' $ k))
  multi (var i) xs k = k (Data.Vec.lookup xs i)
  multi (lit x) xs k = k x

  app→multi : (e : Expr (suc zero)) (s : Code) (k : Code → Set) → lambda e · s $ k → multi e (s ∷ []) k
  app→multi (f · x) s k p = {!!}
  app→multi (var i) s k p = {!!}
  app→multi (lit x) s k p = subst k (sym {!!}) (proj₂ p (proj₁ (proj₁ p)) (proj₂ (proj₁ p)))

  multi→app : (e : Expr (suc zero)) (s : Code) (k : Code → Set) → multi e (s ∷ []) k → lambda e · s $ k
  multi→app (f · x) s k p = {!multi→app f s k ? !}
  multi→app (var zero) s k p = (s , proj₂ lambda1-correct triv) , (λ y q → subst k (sym (invert-triv _ _ (proj₁ lambda1-correct q))) p)
  multi→app (lit x) s k p = (x , proj₂ lambda1-correct triv) , λ y q → subst k (sym (invert-triv _ _ (proj₁ lambda1-correct q))) p

  multi-implies : {n : ℕ} → (f : Expr n) (xs : Vec Code n) (k k' : Code → Set) (h : (y : Code) → k y → k' y) → multi f xs k → multi f xs k'
  multi-implies (f · x) xs k k' h p = multi-implies f xs _ _ (λ y → multi-implies x xs _ _ λ z → implies y z _ _ h) p
  multi-implies (var i) xs k k' h p = h (Data.Vec.lookup xs i) p
  multi-implies (lit x) xs k k' h p = h x p

  liste : {Γ : Cxt} → Env Γ → Code
  liste env = list (go env)
    where
    go : {Γ : Cxt} → Env Γ → List Code
    go {[]}    env = []
    go {τ ∷ Γ} env = env (here refl) ∷ go (λ i → env (there i))

  push : {Γ : Cxt} {τ : Ty} → Env Γ → Code → Env (τ ∷ Γ)
  push env r (here px) = r
  push env r (there i) = env i

  data Unit : Set where
    tt : Unit

  data Bottom : Set where

  ⟦_⟧ : Ty → Code → Set
  ⟦ * ⟧ r = Σ[ n ∈ ℕ ] r ≡ nat n

  _≋[_]_ : Code → Ty → Code → Set
  x ≋[ * ] y = x ≡ y

  eval₀ : {Γ : Cxt} {τ : Ty} → Env Γ → Term Γ τ → Code
  eval₀ env Z       = nat zero
  eval₀ env (S t)   = succ (eval₀ env t)
  eval₀ env (var x) = env x

  _⊩⟨_⟩_ : {Γ : Cxt} → Code → Env Γ → Form Γ → Set
  r ⊩⟨ env ⟩ ⊤ = Unit
  r ⊩⟨ env ⟩ ⊥ = Bottom
  r ⊩⟨ env ⟩ (φ ∧ ψ) = r · zer $ λ s → r · one $ λ t → s ⊩⟨ env ⟩ φ × t ⊩⟨ env ⟩ ψ
  r ⊩⟨ env ⟩ (φ ∨ ψ)
    = r · zer $ λ s → r · one $ λ t → (s ≡ zer × (t ⊩⟨ env ⟩ φ)) ⊎ (s ≡ one × (t ⊩⟨ env ⟩ ψ))
  r ⊩⟨ env ⟩ (φ ⇒ ψ) = (s : Code) → s ⊩⟨ env ⟩ φ → r · s $ λ t → t ⊩⟨ env ⟩ ψ
  r ⊩⟨ env ⟩ (FA {τ} φ) = (s : Code) → ⟦ τ ⟧ s → r · s $ λ t → t ⊩⟨ push env s ⟩ φ
  r ⊩⟨ env ⟩ (EX {τ} φ) = r · zer $ λ s → r · one $ λ t → (⟦ τ ⟧ s × t ⊩⟨ push env s ⟩ φ)
  r ⊩⟨ env ⟩ (x ≈ y) = eval₀ env x ≋[ * ] eval₀ env y
