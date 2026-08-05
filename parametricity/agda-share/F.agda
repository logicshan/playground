
module F where

open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Function
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


Type : ∀ ℓ → Set _
Type ℓ = Set ℓ

Type₀ = Set₀
Type₁ = Set₁

variable
  A B : Type₀
  m n : ℕ

data F : ℕ → Type₀ where
  var : Fin n → F n
  wk : F n → F (suc n)
  _⇒_ : (a b : F n) → F n
  Π : F (suc n) → F n
  sub : F n → F (suc n) → F n


data Bwd (A : Type₀) : Type₀ where
  [] : Bwd A
  _∷_ : Bwd A → A → Bwd A

mapBwd : (A → B) → Bwd A → Bwd B
mapBwd f [] = []
mapBwd f (xs ∷ x) = mapBwd f xs ∷ f x

data Bwds' (A : ℕ → Type₀) : ℕ → Type₀ where
  [] : Bwds' A 0
  _∷_ : Bwds' A n → Bwd (A n) → Bwds' A (suc n)

Bwds : (A : ℕ → Type₀) → ℕ → Type₀
Bwds A n = Bwds' A (suc n)

data Var {n} : Bwd (F n) → F n → Type₀ where
  top : ∀{l a} → Var (l ∷ a) a
  pop : ∀{l a b} → Var l a → Var (l ∷ b) a

data Vars : Bwds F n → F n → Type₀ where
  stop : ∀{ls l a} → Var l a → Vars {n} (ls ∷ l) a
  skip : ∀{ls l a} → Vars ls a → Vars {suc n} (ls ∷ l) (wk a)
  
data Tm {n} : Bwds F n → F n → Type₀ where
  var : ∀{Γ} {a} → Vars Γ a → Tm Γ a
  λ[_]_ : ∀{Γ γ} (a : F n) {b} → Tm (Γ ∷ (γ ∷ a)) b → Tm (Γ ∷ γ) (a ⇒ b)
  _∙_ : ∀{Γ} {a b} → Tm Γ (a ⇒ b) → Tm Γ a → Tm Γ b
  Λ_ : ∀{Γ} {a} → Tm (Γ ∷ []) a → Tm Γ (Π a)
  _⊙_ : ∀{Γ} {a} → Tm Γ (Π a) → (b : F n) → Tm Γ (sub b a)

record F-struc : Type₁ where
  field
    V : Type₀
    El : V → Type₀
    arr : (a b : V) → V
    Pi : (V → V) → V
    lam : ∀{a b} → (El a → El b) → El (arr a b)
    app : ∀{a b} → El (arr a b) → El a → El b
    Lam : ∀{f} → ((v : V) → El (f v)) → El (Pi f)
    App : ∀{f} → El (Pi f) → (v : V) → El (f v)

    βλ : ∀{a b} (f : El a → El b) e → app (lam f) e ≡ f e
    βΛ : ∀{f : V → V} {v} → (e : (v : V) → El (f v)) → App (Lam e) v ≡ e v


module Interp (FS : F-struc) where
  open F-struc FS

  TEnv : ℕ → Type₀
  TEnv zero = ⊤
  TEnv (suc n) = TEnv n × V

  tix : TEnv n → Fin n → V
  tix (_  , v) zero = v
  tix (vs , _) (suc n) = tix vs n

  ⟦_⟧ : F n → TEnv n → V
  ⟦ var x ⟧ e = tix e x
  ⟦ wk a ⟧ (e , _) = ⟦ a ⟧ e
  ⟦ a ⇒ b ⟧ e = arr (⟦ a ⟧ e) (⟦ b ⟧ e)
  ⟦ Π a ⟧ e = Pi (λ v → ⟦ a ⟧ (e , v))
  ⟦ sub b a ⟧ e = ⟦ a ⟧ (e , ⟦ b ⟧ e) 

  Stack : TEnv n → Bwd (F n) → Type₀
  Stack te [] = ⊤
  Stack te (as ∷ a) = Stack te as × El (⟦ a ⟧ te)

  VEnv' : TEnv n → Bwds' F n → Type₀
  VEnv : TEnv n → Bwds F n → Type₀

  VEnv' {zero} _ _ = ⊤
  VEnv' {suc n} (te , _) bs = VEnv te bs 

  VEnv te (bs ∷ b) = VEnv' te bs × Stack te b

  vix : ∀{te : TEnv n} {γ : Bwd (F n)} {a : F n}
      → Var γ a → Stack te γ → El (⟦ a ⟧ te)
  vix top     (_   , e) = e
  vix (pop v) (stk , _) = vix v stk

  vixs : ∀{te : TEnv n} {Γ : Bwds F n} {a : F n}
       → Vars Γ a → VEnv te Γ → El (⟦ a ⟧ te)
  vixs (stop v) ve = vix v (proj₂ ve)
  vixs (skip v) ve = vixs v (proj₁ ve) 


  eval : ∀{Γ : Bwds F n} {a} {te} → (ve : VEnv te Γ) → Tm Γ a → El (⟦ a ⟧ te)
  eval ve (var v) = vixs v ve
  eval (ve , stk) (λ[ a ] e) = lam (λ x → eval (ve , stk , x) e)
  eval ve (f ∙ e) = app (eval ve f) (eval ve e)
  eval ve (Λ e) = Lam (λ v → eval (ve , _) e)
  eval {te = te} ve (e ⊙ v) = App (eval ve e) (⟦ v ⟧ te)


open F-struc

𝔹 : F-struc
𝔹 .V = Bool
𝔹 .El true = ⊤
𝔹 .El false = ⊥
𝔹 .arr false _ = true
𝔹 .arr true  b = b
𝔹 .Pi f = f true ∧ f false
𝔹 .lam {false} {b} f = _
𝔹 .lam {true} {false} f = f _
𝔹 .lam {true} {true} f = _
𝔹 .app {true} {true} f x = _
𝔹 .Lam {f} e with f true | f false | e true | e false
𝔹 .Lam {f} e | true | true | ef | et = _
𝔹 .App {f} e false with f true | f false
𝔹 .App {f} e false | false | false = e
𝔹 .App {f} e false | true | false = e
𝔹 .App {f} e false | true | true = _
𝔹 .App {f} e true with f true | f false
𝔹 .App {f} e true | true | true = e
𝔹 .βλ {true} {false} f e with f e
... | ()
𝔹 .βλ {true} {true} f e = refl
𝔹 .βΛ {f} {false} e with f true | f false | e true | e false
𝔹 .βΛ {f} {false} e | true | true | et | ef = refl
𝔹 .βΛ {f} {true} e with f true | f false | e true | e false
𝔹 .βΛ {f} {true} e | true | true | et | ef = refl

⟨⟩ : Bwds F 0
⟨⟩ = [] ∷ []

open Interp 𝔹

consistent : ¬ Tm ⟨⟩ (Π (var zero))
consistent tm = eval _ tm
