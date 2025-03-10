open import Data.Nat
open import Data.String
open import Data.Bool
open import Data.Fin hiding (_+_)
open import Relation.Nullary.Decidable
import Data.Nat.Properties as ℕ
import Data.Nat.Show as ℕ
import Data.String.Properties as String
open import Agda.Builtin.Equality
open import Function.Base using (case_of_)
open import Agda.Builtin.Maybe
open import Data.Empty using (⊥)
open import Agda.Builtin.List
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Negation using (¬_)
open import Data.Sum
open import Relation.Binary
open import Data.Product

module _ where

module DeBruijnSyntax where
  data Term : Set where
    var : ℕ → Term
    lam : Term → Term
    app : Term → Term → Term

  -- λ f. λ x. f x
  ex : Term
  ex = lam {-f-} (lam {-x-} (app (var {-f-} 1) (var {-x-} 0)))

module LocallyNameless where

  Name = String

  data Term : Set where
    bound : ℕ → Term
    free  : Name → Term
    lam   : Term → Term
    app   : Term → Term → Term
  
  -- openUnder k x t replaces the bound variable at index k in t
  -- with the free variable x
  openUnder : ℕ → Name → Term → Term
  openUnder k x (bound n) =
    if does (k ℕ.≟ n) then free x else bound n
  openUnder k x (free y)  = free y
  openUnder k x (lam u)   = lam (openUnder (suc k) x u)
  openUnder k x (app u v) =
    app (openUnder k x u) (openUnder k x v)

  openT = openUnder 0

  -- closeUnder k x t replaces all free variables named x in t
  -- with the bound variable at index k
  closeUnder : ℕ → Name → Term → Term
  closeUnder k x (bound n) = bound n
  closeUnder k x (free y)  =
    if does (x String.≟ y) then bound k else free y
  closeUnder k x (lam u)   = lam (closeUnder (suc k) x u)
  closeUnder k x (app u v) =
    app (closeUnder k x u) (closeUnder k x v)

  closeT = closeUnder 0

  ex = lam (closeT "f" (
         lam (closeT "x" (
           app (free "f") (free "x")
         ))
       ))

  _ : ex ≡ lam (lam (app (bound 1) (bound 0)))
  _ = refl

module ‶HOAS″ where
  {-# NO_POSITIVITY_CHECK #-}
  data Term : Set where
    lam : (Term → Term) → Term
    app : Term → Term → Term

  ex : Term
  ex = lam (λ f → lam (λ x → app f x))

  exotic : Term
  exotic = lam (λ x → case x of λ where
                        (lam _)   → x
                        (app _ _) → lam (λ y → y))

module PHOAS where
  data Term (V : Set) : Set where
    var : V → Term V
    lam : (V → Term V) → Term V
    app : Term V → Term V → Term V

  ex : ∀ {V} → Term V
  ex = lam (λ f → lam (λ x → app (var f) (var x)))

  pp : ℕ → Term String → String
  pp fresh (var x)    = x
  pp fresh (lam f)    =
    let name = "x" ++ ℕ.show fresh
    in  "λ " ++ name ++ ". " ++ pp (suc fresh) (f name)
  pp fresh (app u v)  = case u of λ where
    (var x) → x ++ " " ++ pp fresh v
    _       → "(" ++ pp fresh u ++ ") " ++ pp fresh v

  _ : pp 0 ex ≡ "λ x0. λ x1. x0 x1"
  _ = refl

module WellScopedDB where
  data Term (n : ℕ) : Set where
    var : Fin n → Term n
    lam : Term (1 + n) → Term n
    app : Term n → Term n → Term n

  ex : Term 0
  ex = lam {-f-} (
         lam {-x-} (
           app (var {-f-} (suc zero))
               (var {-x-} zero)
         )
       )

module PoorMansWellScoped where
  data Term (V : Set) : Set where
    var : V → Term V
    lam : Term (Maybe V) → Term V
    app : Term V → Term V → Term V

  ex : Term ⊥
  ex = lam {-f-} (
         lam {-x-} (
           app (var {-f-} (just nothing))
               (var {-x-} nothing)
         )
       )

module WellScopedNames where
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)

  Scope = List String

  data Term (s : Scope) : Set where
    var : (x : String) → x ∈ s → Term s
    lam : (x : String) → Term (x ∷ s) → Term s
    app : Term s → Term s → Term s

  ex : Term []
  ex = lam "f" (
         lam "x" (
           app (var "f" (there (here refl)))
               (var "x" (here refl))
         )
       )

  ex' : Term []
  ex' = lam "x" (
          lam "x" (
            app (var "x" (there (here refl)))
                (var "x" (here refl))
          )
        )

module WellScopedFresh where

  data FreshList (A : Set) : Set
  _#_ : {A : Set} → A → FreshList A → Set

  data FreshList A where
    []    : FreshList A
    _∷_<_> : (x : A) (xs : FreshList A) → x # xs → FreshList A

  x # [] = ⊤
  x # (y ∷ xs < _ >) = x ≢ y × (x # xs)

  data _∈_ {A : Set} (x : A) : FreshList A → Set where
    here  : ∀ {xs p} → x ∈ (x ∷ xs < p >)
    there : ∀ {y xs p} → x ∈ xs → x ∈ (y ∷ xs < p >)

  Scope = FreshList String

  data Term (s : Scope) : Set where
    var : (x : String) → x ∈ s → Term s
    lam : (x : String) (p : x # s)
        → Term (x ∷ s < p >) → Term s
    app : Term s → Term s → Term s

  ex : Term []
  ex = lam "f" f# (
         lam "x" x#f (
           app (var "f" (there here))
               (var "x" here)
         )
       )
    where
      f# : "f" # []
      f# = tt

      x#f : "x" # ("f" ∷ [] < f# >)
      x#f = (λ ()) , tt

module NamelessPainless where

  record NaPa : Set₁ where
    field
      World   : Set
      ∅       : World
      _↑1     : World → World
      Name    : World → Set
      _⊆_     : World → World → Set
      zeroᴺ   : ∀ {α} → Name (α ↑1)
      sucᴺ    : ∀ {α} → Name α → Name (α ↑1)
      _==ᴺ_   : ∀ {α} → Name α → Name α → Bool
      exportᴺ : ∀ {α} → Name (α ↑1) → Maybe (Name α)
      coerce  : ∀ {α β} → α ⊆ β → Name α → Name β
      ¬Name∅  : ¬ (Name ∅)


  open NaPa ⦃...⦄

  module _ ⦃ _ : NaPa ⦄ where

    data Term (w : World) : Set where
      var : Name w → Term w
      lam : Term (w ↑1) → Term w
      app : Term w → Term w → Term w

    ex : ∀ {w} → Term w
    ex = lam {-f-} (
           lam {-x-} (
             app (var {-f-} (sucᴺ zeroᴺ))
                 (var {-x-} zeroᴺ)
            )
          )

module AbstractScopeGraphs where

  Name = String -- just for concreteness

  record ScopeGraph : Set₁ where
    field
      -- Structure of scope graphs we rely on:
      -- 1. a type of scopes (i.e. nodes in the graph)
      Scope : Set
      -- 2. a predicate expressing reachability + visibility
      _∈_   : Name → Scope → Set
      -- 3. Binding a name, shadowing all previous occurrences
      bind  : Name → Scope → Scope
      here  : ∀ {x s} → x ∈ bind x s
      there : ∀ {x y s} → x ≢ y → x ∈ s → x ∈ bind y s

  open ScopeGraph ⦃...⦄

  module _ ⦃ _ : ScopeGraph ⦄ where

    data Term (s : Scope) : Set where
      var : (x : Name) → x ∈ s → Term s
      lam : (x : Name) → Term (bind x s) → Term s
      app : Term s → Term s → Term s

    ex : ∀ {s} → Term s
    ex {s} = lam "f" (
               lam "x" (
                 app (var "f" (there (λ ()) here))
                     (var "x" here)
               )
             )

module NamelyPainless where

  record NomPa : Set₁ where

    field
      World  : Set
      Name   : World → Set
      Binder : Set
      _◃_    : Binder → World → World

      zeroᴮ  : Binder
      sucᴮ   : Binder → Binder

      nameᴮ   : ∀ {α} b → Name (b ◃ α)
      binderᴺ : ∀ {α} → Name α → Binder

      ∅      : World
      ¬Name∅ : ¬ (Name ∅)

      _==ᴺ_   : ∀ {α} (x y : Name α) → Bool
      exportᴺ : ∀ {α b} → Name (b ◃ α)
              → Name (b ◃ ∅) ⊎ Name α

      _#_  : Binder → World → Set
      _#∅  : ∀ b → b # ∅
      suc# : ∀ {α b} → b # α → (sucᴮ b) # (b ◃ α)

      _⊆_     : World → World → Set
      coerceᴺ : ∀ {α b} → α ⊆ b → Name α → Name b
      ⊆-refl  : Reflexive _⊆_
      ⊆-trans : Transitive _⊆_
      ⊆-∅     : ∀ {α} → ∅ ⊆ α
      ⊆-◃     : ∀ {α β} b → α ⊆ β → (b ◃ α) ⊆ (b ◃ β)
      ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◃ α)

  open NomPa {{...}}

  module Syntax {{_ : NomPa}} where

    data Term (w : World) : Set where
      var : Name w → Term w
      lam : (b : Binder) → Term (b ◃ w) → Term w
      app : Term w → Term w → Term w

    ex : Term ∅
    ex = lam fb (lam xb (app (var f) (var x)))
      where
        fb xb : Binder
        fb = zeroᴮ
        xb = sucᴮ zeroᴮ

        x-fresh : xb # (fb ◃ ∅)
        x-fresh = suc# (fb #∅)

        f = coerceᴺ (⊆-# x-fresh) (nameᴮ fb)
        x = nameᴮ xb

  module NominalNomPa {{_ : NomPa}} where
    Sort : Set₁
    Sort = World → Set

    Atom : Sort
    Atom = Name

    1ᵉ : Sort
    1ᵉ _ = ⊤

    _×ᵉ_ : Sort → Sort → Sort
    (E₁ ×ᵉ E₂) a = E₁ a × E₂ a

    _→ᵉ_ : Sort → Sort → Set
    (E₁ →ᵉ E₂) = ∀ {a} → E₁ a → E₂ a

    Pred   : Sort → Set₁
    Pred E = ∀ {a} → E a → Set

    absᵉ : Sort → Sort
    (absᵉ E) a = Σ[ b ∈ Binder ] (E (b ◃ a))

    data Term : Sort where
      var : Atom →ᵉ Term
      app : (Term ×ᵉ Term) →ᵉ Term
      lam : (absᵉ Term) →ᵉ Term

module CoDeBruijn where

  variable
    k l m n : ℕ

  data Cover : (k l m : ℕ) → Set where
    done   :               Cover      0       0       0
    left   : Cover k l m → Cover (suc k)      l  (suc m)
    right  : Cover k l m → Cover      k  (suc l) (suc m)
    both   : Cover k l m → Cover (suc k) (suc l) (suc m)

  data Term : ℕ → Set where
    var  : Term 1
    lam  : Term (suc n) → Term n
    lam' : Term n → Term n  -- argument is not used
    app  : Cover k l m → Term k → Term l → Term m

  ex : Term 0
  ex = lam {-f-} (
         lam {-x-} (
           app (right (left done))
               (var {-f-}) (var {-x-})
         )
       )

module NamedCoDeBruijn where

  Name  = String
  Scope = List Name

  variable
    x y z    : Name
    xs ys zs : Scope

  data Cover : (xs ys zs : Scope) → Set where
    done   :                  Cover      []       []       []
    left   : Cover xs ys zs → Cover (z ∷ xs)      ys  (z ∷ zs)
    right  : Cover xs ys zs → Cover      xs  (z ∷ ys) (z ∷ zs)
    both   : Cover xs ys zs → Cover (z ∷ xs) (z ∷ ys) (z ∷ zs)

  data Term : Scope → Set where
    var  : (x : Name) → Term (x ∷ [])
    lam  : (x : Name) → Term (x ∷ xs) → Term xs
    lam' : (x : Name) → Term xs → Term xs
    app  : Cover xs ys zs → Term xs → Term ys → Term zs

  ex : Term []
  ex = lam "f" (
         lam "x" (
           app (right (left done))
               (var "f") (var "x")
         )
       )
