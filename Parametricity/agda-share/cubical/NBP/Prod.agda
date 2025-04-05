
module NBP.Prod where

open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import NBP.Prod.Types
open import NBP.Prod.Terms.Core as Terms
open import NBP.Prod.Terms as Terms
import NBP.Prod.Terms.Levels as Terms

open Rn-Stx
open Rn-Sem

record Psh : Type₁ where
  no-eta-equality
  field
    ⟨_⟩ : Cx → Type
    isSet-⟨_⟩ : ∀ Γ → isSet (⟨_⟩ Γ)
    ren : Rn Γ Δ → ⟨_⟩ Δ → ⟨_⟩ Γ
    ren-id : ∀(x : ⟨_⟩ Γ) → ren rn-id x ≡ x
    ren-∘ : ∀(ρ : Rn Γ Δ) (σ : Rn Δ Θ) x
          → ren (ρ rn∘ σ) x ≡ ren ρ (ren σ x)

open Psh

Va : Ty → Psh
⟨ Va A ⟩ Γ = A ∈ Γ
isSet-⟨ Va A ⟩ Γ = isSet-∈ A Γ
Va A .ren ρ = rn-∈ ρ
Va A .ren-id v = refl
Va A .ren-∘ ρ σ v = refl

Tm : Ty → Psh
⟨ Tm A ⟩ Γ = Stx.Tm Γ A
isSet-⟨ Tm A ⟩ Γ = Terms.isSet-Tm Γ A
Tm A .ren = rn-tm
Tm A .ren-id = rn-tm-id
Tm A .ren-∘ ρ σ = rn-tm-∘

No : Ty → Psh
⟨ No A ⟩ Γ = Sem.No Γ A
isSet-⟨ No A ⟩ Γ = Terms.isSet-No Γ A
No A .ren = rn-no
No A .ren-id = rn-no-id
No A .ren-∘ = rn-no-∘

Ne : Ty → Psh
⟨ Ne A ⟩ Γ = Sem.Ne Γ A
isSet-⟨ Ne A ⟩ Γ = Terms.isSet-Ne Γ A
Ne A .ren = rn-ne
Ne A .ren-id = rn-ne-id
Ne A .ren-∘ = rn-ne-∘

En : Cx → Psh
⟨ En Δ ⟩ Γ = Env.En Γ Δ
isSet-⟨ En Δ ⟩ Γ = Env.isSet-En Γ Δ
En Γ .ren = Env.rn-en
En Γ .ren-id = Env.rn-en-id
En Γ .ren-∘ = Env.rn-en-∘

infix 10 _⊢_
record _⊢_ (A B : Psh) : Type where
  field
    tr : ⟨ A ⟩ Γ → ⟨ B ⟩ Γ
    na : ∀(ρ : Rn Γ Δ) x → B .ren ρ (tr x) ≡ tr (A .ren ρ x)
open _⊢_

id̂ : ∀{A} → A ⊢ A
id̂ .tr x = x
id̂ .na ρ x = refl

isSet-_⊢_ : ∀ A B
          → isSet (A ⊢ B)
isSet- A ⊢ B = isSetRetract yabba dabba (λ x → refl) isSet-⊢Σ
  where
  Tr : Type
  Tr = ∀ Γ → ⟨ A ⟩ Γ → ⟨ B ⟩ Γ
  ⊢Σ = Σ[ f ∈ Tr ] ∀ Γ Δ (ρ : Rn Γ Δ) x → B .ren ρ (f Δ x) ≡ f Γ (A .ren ρ x)

  isSet-⊢Σ : isSet ⊢Σ
  isSet-⊢Σ =
    isSetΣSndProp
      (isSetΠ (λ _ → isSet→ (isSet-⟨ B ⟩ _)))
      λ f → isPropΠ λ Γ → isPropΠ λ Δ → isPropΠ λ ρ → isPropΠ λ x →
        (isSet-⟨ B ⟩ Γ) (B .ren ρ (f Δ x)) (f Γ (A .ren ρ x))

  yabba : A ⊢ B → ⊢Σ
  yabba f .fst _ = f .tr
  yabba f .snd _ _ = f .na

  dabba : ⊢Σ → A ⊢ B
  dabba f .tr = f .fst _
  dabba f .na = f .snd _ _

よ : Cx → Psh
⟨ よ Γ ⟩ Δ = Rn Δ Γ
isSet-⟨ よ Γ ⟩ Δ = isSet-Rn Δ Γ
よ Γ .ren = _rn∘_
よ Γ .ren-id ρ = refl
よ Γ .ren-∘ ρ σ τ = refl

vâ : Va A ⊢ Ne A
vâ .tr v = Sem.va v
vâ .na ρ v = refl

infixr 7 _∘̂_
_∘̂_ : ∀{A B C} → B ⊢ C → A ⊢ B → A ⊢ C
(g ∘̂ f) .tr = g .tr ∘ f .tr
(g ∘̂ f) .na ρ x = g .na _ _ ∙ cong (tr g) (f .na ρ x)

infixr 15 _̂×_
_̂×_ : Psh → Psh → Psh
⟨ A ̂× B ⟩ Γ = ⟨ A ⟩ Γ × ⟨ B ⟩ Γ
isSet-⟨ A ̂× B ⟩ Γ = isSet× (isSet-⟨ A ⟩ Γ) (isSet-⟨ B ⟩ Γ)
(A ̂× B) .ren ρ (x , y) = A .ren ρ x , B .ren ρ y
(A ̂× B) .ren-id (x , y) = cong₂ _,_ (A .ren-id x) (B .ren-id y)
(A ̂× B) .ren-∘ ρ σ (x , y) i
  = λ where .fst → A .ren-∘ ρ σ x i
            .snd → B .ren-∘ ρ σ y i

⟨_↓_⟩ : ∀{A B C} → A ⊢ B → A ⊢ C → A ⊢ B ̂× C
⟨ f ↓ g ⟩ .tr x = f .tr x , g .tr x
⟨ f ↓ g ⟩ .na ρ x
  = cong₂ _,_ (f .na ρ x) (g .na ρ x)

⟨_↑_⟩ : ∀{A B C D} → A ⊢ C → B ⊢ D → A ̂× B ⊢ C ̂× D
⟨ f ↑ g ⟩ .tr (x , y) = f .tr x , g .tr y
⟨ f ↑ g ⟩ .na ρ (x , y)
  = cong₂ _,_ (f .na ρ x) (g .na ρ y)

fŝt : ∀{A B} → A ̂× B ⊢ A
fŝt .tr = fst
fŝt .na _ _ = refl

sn̂d : ∀{A B} → A ̂× B ⊢ B
sn̂d .tr = snd
sn̂d .na _ _ = refl

infixr 11 _̂⇒_
_̂⇒_ : Psh → Psh → Psh
⟨ A ̂⇒ B ⟩ Γ = よ Γ ̂× A ⊢ B
isSet-⟨ A ̂⇒ B ⟩ Γ = isSet- _ ⊢ B
(A ̂⇒ B) .ren ρ f = λ where
  .tr (σ , x) → f .tr (σ rn∘ ρ , x)
  .na τ (σ , x) → f .na τ (σ rn∘ ρ , x) 
(A ̂⇒ B) .ren-id f = refl
(A ̂⇒ B) .ren-∘ ρ σ f = refl

λ̂ : ∀{A B C} → A ̂× B ⊢ C → A ⊢ B ̂⇒ C
λ̂ {A = A} {B} f .tr x = λ where
  .tr (ρ , y) → f .tr (A .ren ρ x , y)
  .na ρ (σ , y) →
    let h = λ z → f .tr (z , B .ren ρ y) in
      f .na ρ (A .ren σ x , y)
    ∙ cong h (sym (A .ren-∘ ρ σ x))
λ̂ {A = A} {B} {C} f .na ρ x i = λ where
  .tr (σ , y) → f .tr (A .ren-∘ σ ρ x i , y)
  .na σ (τ , y) →
    let h = λ z → f .tr (z , B .ren σ y) in
    isSet→isSet' (isSet-⟨ C ⟩ _)
      (f .na σ (A .ren (τ rn∘ ρ) x , y) ∙ cong h (sym (A .ren-∘ σ (τ rn∘ ρ) x)))
      (f .na σ (A .ren τ (A .ren ρ x) , y) ∙ cong h (sym (A .ren-∘ σ τ (A .ren ρ x))))
      (cong (C .ren σ ∘ f .tr ∘ (_, y)) (A .ren-∘ τ ρ x))
      (cong h (A .ren-∘ (σ rn∘ τ) ρ x))
      i

ε̂ : ∀ A B → (A ̂⇒ B) ̂× A ⊢ B
ε̂ A B .tr (f , x) = f .tr (rn-id , x)
ε̂ A B .na ρ (f , x) = f .na ρ (rn-id , x)

pre : ∀ A B C → A ⊢ B → B ̂⇒ C ⊢ A ̂⇒ C
pre A B C f .tr {Γ = Γ} g = g ∘̂ ⟨ id̂ {よ Γ} ↑ f ⟩ 
pre A B C f .na ρ p = refl

infixr 14 _̂+_
_̂+_ : Psh → Psh → Psh
⟨ A ̂+ B ⟩ Γ = ⟨ A ⟩ Γ ⊎ ⟨ B ⟩ Γ
isSet-⟨ A ̂+ B ⟩ Γ = isSet⊎ (isSet-⟨ A ⟩ Γ) (isSet-⟨ B ⟩ Γ)
(A ̂+ B) .ren ρ (inl x) = inl (A .ren ρ x)
(A ̂+ B) .ren ρ (inr x) = inr (B .ren ρ x)
(A ̂+ B) .ren-id (inl x) = cong inl (A .ren-id x)
(A ̂+ B) .ren-id (inr x) = cong inr (B .ren-id x)
(A ̂+ B) .ren-∘ ρ σ (inl x) = cong inl (A .ren-∘ ρ σ x)
(A ̂+ B) .ren-∘ ρ σ (inr x) = cong inr (B .ren-∘ ρ σ x)

⊤̂ : Psh
⟨ ⊤̂ ⟩ _ = Unit
isSet-⟨ ⊤̂ ⟩ _ = isSetUnit
⊤̂ .ren _ _ = _
⊤̂ .ren-id _ = refl
⊤̂ .ren-∘ _ _ _ = refl

! : ∀{A} → A ⊢ ⊤̂
! .tr _ = _
! .na _ _ = refl

⟦_⟧ : Ty → Psh
⟦ ⊤ ⟧ = ⊤̂
⟦ β ⟧ = No β
⟦ S * T ⟧ = ⟦ S ⟧ ̂× ⟦ T ⟧
⟦ S ⇒ T ⟧ = ⟦ S ⟧ ̂⇒ ⟦ T ⟧

⟪_⟫ : Cx → Psh
⟪ [] ⟫ = ⊤̂
⟪ Γ ∷ A ⟫ = ⟪ Γ ⟫ ̂× ⟦ A ⟧

module Quote where
  open Stx hiding (Tm)
  open Sem hiding (No; Ne)

  tr-no : ⟨ No A ⟩ Γ → ⟨ Tm A ⟩ Γ
  tr-ne : ⟨ Ne A ⟩ Γ → ⟨ Tm A ⟩ Γ
  
  na-no : ∀(e : ⟨ No A ⟩ Γ) → Tm A .ren ρ (tr-no e) ≡ tr-no (No A .ren ρ e)
  na-ne : ∀(e : ⟨ Ne A ⟩ Γ) → Tm A .ren ρ (tr-ne e) ≡ tr-ne (Ne A .ren ρ e)

  tr-no tt = tt
  tr-no (l , r) = tr-no l , tr-no r
  tr-no (la e) = la (tr-no e)
  tr-no (ne e) = tr-ne e

  tr-ne (va v) = va v
  tr-ne (π₁ p) = π₁ (tr-ne p)
  tr-ne (π₂ p) = π₂ (tr-ne p)
  tr-ne (f $ e) = tr-ne f $ tr-no e

  na-no tt = refl
  na-no (l , r) = cong₂ _,_ (na-no l) (na-no r)
  na-no (la e) = cong la (na-no e)
  na-no (ne e) = na-ne e

  na-ne (va v) = refl
  na-ne (π₁ p) = cong π₁ (na-ne p)
  na-ne (π₂ p) = cong π₂ (na-ne p)
  na-ne (f $ e) = cong₂ _$_ (na-ne f) (na-no e)

  λⁿᶠ : Va A ̂⇒ No B ⊢ No (A ⇒ B)
  λⁿᶠ .tr f = la (f .tr (rn-π , to))
  λⁿᶠ .na ρ f i = la (f .na (sh ρ) (rn-π , to) i)

quot-no : No A ⊢ Tm A
quot-no .tr = Quote.tr-no
quot-no .na _ = Quote.na-no

quot-ne : Ne A ⊢ Tm A
quot-ne .tr = Quote.tr-ne
quot-ne .na _ = Quote.na-ne

module Eval where
  ix-tr : A ∈ Γ → ⟨ ⟪ Γ ⟫ ⟩ Δ → ⟨ ⟦ A ⟧ ⟩ Δ
  ix-tr to     (_ , e) = e
  ix-tr (po v) (γ , _) = ix-tr v γ

  ix-na : (v : A ∈ Γ) → (ρ : Rn Θ Δ) (γ : ⟨ ⟪ Γ ⟫ ⟩ Δ)
        → ⟦ A ⟧ .ren ρ (ix-tr v γ) ≡ ix-tr v (⟪ Γ ⟫ .ren ρ γ)
  ix-na to     ρ γ = refl
  ix-na (po v) ρ (γ , _) = ix-na v ρ γ

  ix : A ∈ Γ → ⟪ Γ ⟫ ⊢ ⟦ A ⟧
  ix v .tr = ix-tr v
  ix v .na = ix-na v

  open Stx hiding (Tm)
  open Sem hiding (No; Ne)

  eval : Stx.Tm Γ A → ⟪ Γ ⟫ ⊢ ⟦ A ⟧
  eval (va v) = ix v
  eval tt = !
  eval (l , r) = ⟨ eval l ↓ eval r ⟩
  eval (π₁ e) = fŝt ∘̂ eval e
  eval (π₂ e) = sn̂d ∘̂ eval e
  eval (la e) = λ̂ (eval e)
  eval (f $ e) = ε̂ _ _ ∘̂ ⟨ eval f ↓ eval e ⟩

  neu : Ne A ⊢ No A
  neu .tr = ne
  neu .na ρ e = refl

  u : ∀ A → Ne A ⊢ ⟦ A ⟧
  norm : ∀ A → ⟦ A ⟧ ⊢ No A

  private
    u-norm : ∀ A B → ⟦ A ⟧ ̂⇒ ⟦ B ⟧ ⊢ Va A ̂⇒ No B
    u-norm A B =
      λ̂ {⟦ A ⟧ ̂⇒ ⟦ B ⟧} {Va A} {No B}
        (norm B ∘̂ ε̂ (Va A) ⟦ B ⟧ ∘̂ ⟨ pre (Va A) ⟦ A ⟧ ⟦ B ⟧ (u A ∘̂ vâ) ↑ id̂ ⟩) 

  norm ⊤ .tr _ = Sem.tt
  norm ⊤ .na _ _ = refl

  norm β = id̂

  norm (A * B) .tr (x , y) = norm A .tr x , norm B .tr y
  norm (A * B) .na ρ (x , y) i =
    norm A .na ρ x i , norm B .na ρ y i

  norm (A ⇒ B) = Quote.λⁿᶠ ∘̂ u-norm A B

  private
    -- Factoring this out because it's large and used repeatedly.
    u-ap : ∀ A B → ⟨ ⟦ A ⟧ ⟩ Δ → ⟨ Ne (A ⇒ B) ⟩ Δ → ⟨ ⟦ B ⟧ ⟩ Δ
    u-ap A B x f = u B .tr (f $ norm A .tr x)
    
    u-⇒-tr : ∀ A B → ⟨ Ne (A ⇒ B) ⟩ Γ → Rn Δ Γ → ⟨ ⟦ A ⟧ ⟩ Δ → ⟨ ⟦ B ⟧ ⟩ Δ
    u-⇒-tr A B f ρ x = u-ap A B x (rn-ne ρ f)

    u-⇒-na : ∀ A B
           → (f : ⟨ Ne (A ⇒ B) ⟩ Γ)
           → (ρ : Rn Θ Δ) → (σ : Rn Δ Γ)
           → (x : ⟨ ⟦ A ⟧ ⟩ Δ)
           → ⟦ B ⟧ .ren ρ (u-⇒-tr A B f σ x)
           ≡ u-⇒-tr A B f (ρ rn∘ σ) (⟦ A ⟧ .ren ρ x)
    u-⇒-na A B f ρ σ x
      = u B .na ρ (rn-ne σ f $ norm A .tr x)
      ∙ cong₂ h (sym (rn-ne-∘ ρ σ f)) (norm A .na ρ x)
      where h = λ g y → u B .tr (g $ y)

  u ⊤ = !

  u β = neu

  u (A * B) .tr p = λ where
    .fst → u A .tr (π₁ p)
    .snd → u B .tr (π₂ p)
  u (A * B) .na ρ p i = λ where
    .fst → u A .na ρ (π₁ p) i
    .snd → u B .na ρ (π₂ p) i

  u (A ⇒ B) .tr f .tr (ρ , x) = u-⇒-tr A B f ρ x
  u (A ⇒ B) .tr f .na ρ (σ , x) = u-⇒-na A B f ρ σ x
  u (A ⇒ B) .na ρ f j = λ where
    .tr (σ , x) → u B .tr (rn-ne-∘ σ ρ f j $ norm A .tr x)
    .na τ (σ , x) →
      isSet→isSet' (isSet-⟨ ⟦ B ⟧ ⟩ _)
        (u-⇒-na A B f τ (σ rn∘ ρ) x)
        (u-⇒-na A B (rn-ne ρ f) τ σ x)
        (cong (⟦ B ⟧ .ren τ ∘ u-ap A B x) (rn-ne-∘ σ ρ f))
        (cong (u-ap A B (⟦ A ⟧ .ren τ x)) (rn-ne-∘ (τ rn∘ σ) ρ f))
        j

normalize₀ : Stx.Tm [] A → Stx.Tm [] A
normalize₀ {A} e = (quot-no ∘̂ Eval.norm A ∘̂ Eval.eval e) .tr tt
