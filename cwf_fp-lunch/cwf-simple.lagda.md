What is a simply typed CWF?

```
module cwf-simple where

open import Relation.Binary.PropositionalEquality hiding ([_])

record CwF-simple : Set₁ where
  field
    Con : Set
    Ty : Set
    Tm : Con → Ty → Set
    Tms : Con → Con → Set
    -- Con,Tms are a category
    id : {Γ : Con} → Tms Γ Γ
    _∘_ : {Γ Δ Θ : Con} → Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
    idl : ∀ {Γ Δ}{δ : Tms Γ Δ} → id ∘ δ ≡ δ
    idr : ∀ {Γ Δ}{δ : Tms Γ Δ} → δ ∘ id ≡ δ
    ass : ∀ {Γ Δ Θ Ξ}{ξ : Tms Θ Ξ}{θ : Tms Δ Θ}{δ : Tms Γ Δ}
          → (ξ ∘ θ) ∘ δ ≡ ξ ∘ (θ ∘ δ)
    -- Tm _ A is a presheaf
    _[_] : ∀ {Γ Δ A} → Tm Γ A → Tms Δ Γ → Tm Δ A
    [id] : ∀ {Γ A}{t : Tm Γ A} →  (t [ id ]) ≡ t
    [∘] : ∀ {Γ Δ Θ}{A : Ty}{t : Tm Θ A}{θ : Tms Δ Θ}{δ : Tms Γ Δ} →
            t [ θ ] [ δ ] ≡ t [ θ ∘ δ ]
            --  (_[ δ ] ∘ _[ θ ]) = _[ θ ∘ δ ]
    -- empty context
    • : Con
    ε : {Γ : Con} → Tms Γ • 
    •-η : {Γ : Con}{δ : Tms Γ •} → δ ≡ ε
    -- context extension
    _▷_ : Con → Ty → Con
    _,_ : ∀ {Γ Δ A} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ ▷ A)
    π₀ : ∀ {Γ Δ A} → Tms Γ (Δ ▷ A) → Tms Γ Δ
    π₁ : ∀ {Γ Δ A} → Tms Γ (Δ ▷ A) → Tm Γ A
    ▷-β₀ : ∀ {Γ Δ A}{δ : Tms Γ Δ}{t : Tm Γ A}
           → π₀ (δ , t) ≡ δ
    ▷-β₁ : ∀ {Γ Δ A}{δ : Tms Γ Δ}{t : Tm Γ A}
           → π₁ (δ , t) ≡ t
    ▷-η : ∀ {Γ Δ A}{δ : Tms Γ (Δ ▷ A)}
           → (π₀ δ , π₁ δ) ≡ δ
    π₀∘ : ∀ {Γ Δ Θ}{A : Ty}{θ : Tms Δ (Θ ▷ A)}{δ : Tms Γ Δ}
           → π₀ (θ ∘ δ) ≡ π₀ θ ∘ δ
    π₁∘ : ∀ {Γ Δ Θ}{A : Ty}{θ : Tms Δ (Θ ▷ A)}{δ : Tms Γ Δ}
           → π₁ (θ ∘ δ) ≡ (π₁ θ) [ δ ]         
```

Semantics
```
open import Data.Unit
open import Data.Product

data U : Set where
  ⊤U : U
  _×U_ : U → U → U 

El : U → Set
El ⊤U = ⊤
El (A ×U B) = El A × El B

open CwF-simple

model : CwF-simple
Con model = U
Ty model = U
Tm model Γ A = El Γ → El A
Tms model Γ Δ = El Γ → El Δ
id model x = x
_∘_ model f g x = f (g x)
idl model = refl
idr model = refl
ass model = refl
_[_] model f g x = f (g x)
[id] model = refl
[∘] model = refl
• model = ⊤U
ε model = λ x → tt
•-η model = refl
_▷_ model A B = A ×U B
CwF-simple._,_ model f g x = (f x) Data.Product., (g x)
π₀ model f x = proj₁ (f x)
π₁ model f x  = proj₂ (f x)
▷-β₀ model = refl
▷-β₁ model = refl
▷-η model = refl
π₀∘ model = refl
π₁∘ model = refl
```
