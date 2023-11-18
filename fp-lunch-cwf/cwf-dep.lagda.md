What is a simply typed CWF?

```
module cwf-dep where

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

-- heterogenous equality
infix 2 _⊢_≡[_]≡_
data _⊢_≡[_]≡_ {X : Set}(F : X → Set) : {x y : X} → F x → x ≡ y → F y → Set where
  refl : {x : X}{z : F x} → F ⊢ z ≡[ refl ]≡ z


record CwF : Set₁ where
  field
    Con : Set
    Tms : Con → Con → Set
    -- Con,Tms are a category
    id : {Γ : Con} → Tms Γ Γ
    _∘_ : {Γ Δ Θ : Con} → Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
    idl : ∀ {Γ Δ}{δ : Tms Γ Δ} → id ∘ δ ≡ δ
    idr : ∀ {Γ Δ}{δ : Tms Γ Δ} → δ ∘ id ≡ δ
    ass : ∀ {Γ Δ Θ Ξ}{ξ : Tms Θ Ξ}{θ : Tms Δ Θ}{δ : Tms Γ Δ}
          → (ξ ∘ θ) ∘ δ ≡ ξ ∘ (θ ∘ δ)
    -- Ty is a presheaf
    Ty : Con → Set
    _[_]T : ∀ {Γ Δ} → Ty Γ → Tms Δ Γ → Ty Δ
    [id]T : ∀ {Γ}{A : Ty Γ} → (A [ id ]T) ≡ A
    [∘]T : ∀ {Γ Δ Θ}{A : Ty Θ}{θ : Tms Δ Θ}{δ : Tms Γ Δ} →
            A [ θ ∘ δ ]T ≡ A [ θ ]T [ δ ]T 
    -- Tm is a dependent presheaf over Ty
    -- or in other words a presheaf over ∫ Ty 
    Tm : (Γ : Con) → Ty Γ → Set
    _[_]t : ∀ {Γ Δ A} → Tm Γ A → (γ : Tms Δ Γ) → Tm Δ (A [ γ ]T)
    [id]t : ∀ {Γ}{A : Ty Γ}{a : Tm Γ A} → (λ A → Tm Γ A) ⊢ (a [ id {Γ = Γ} ]t) ≡[ [id]T ]≡ a
    [∘]t : ∀ {Γ Δ Θ}{A : Ty Θ}{a : Tm Θ A}{θ : Tms Δ Θ}{δ : Tms Γ Δ}
            → (λ A → Tm Γ A) ⊢ (a [ θ ∘ δ ]t) ≡[ [∘]T ]≡ a [ θ ]t [ δ ]t
    -- empty context
    • : Con
    ε : {Γ : Con} → Tms Γ • 
    •-η : {Γ : Con}{δ : Tms Γ •} → δ ≡ ε
    -- context extension
    _▷_ : (Γ : Con) → Ty Γ → Con
    _,_ : ∀ {Γ Δ A} → (δ : Tms Γ Δ) → Tm Γ (A [ δ ]T) → Tms Γ (Δ ▷ A)    
    π₀ : ∀ {Γ Δ A} → Tms Γ (Δ ▷ A) → Tms Γ Δ
    π₁ : ∀ {Γ Δ A} → (δ : Tms Γ (Δ ▷ A)) → Tm Γ (A [ π₀ δ ]T)
    ▷-β₀ : ∀ {Γ Δ A}{δ : Tms Γ Δ}{a : Tm Γ (A [ δ ]T) }
           → π₀ (δ , a) ≡ δ
    ▷-β₁ : ∀ {Γ Δ A}{δ : Tms Γ Δ}{a : Tm Γ (A [ δ ]T)}
           → (λ δ → Tm Γ (A [ δ ]T)) ⊢ π₁ (δ , a) ≡[ ▷-β₀ ]≡ a
    ▷-η : ∀ {Γ Δ A}{δ : Tms Γ (Δ ▷ A)}
           → (π₀ δ , π₁ δ) ≡ δ
    π₀∘ : ∀ {Γ Δ Θ}{A : Ty Θ}{θ : Tms Δ (Θ ▷ A)}{δ : Tms Γ Δ}
           → π₀ (θ ∘ δ) ≡ π₀ θ ∘ δ
    π₁∘ : ∀ {Γ Δ Θ}{A : Ty Θ}{θ : Tms Δ (Θ ▷ A)}{δ : Tms Γ Δ}
           → let aux : A [ π₀ (θ ∘ δ) ]T ≡ (A [ π₀ θ ]T) [ δ ]T
                 aux =  A [ π₀ (θ ∘ δ) ]T
                        ≡⟨ cong (λ δ → A [ δ ]T) π₀∘ ⟩ (A [ (π₀ θ) ∘ δ ]T)
                        ≡⟨ [∘]T ⟩ (A [ π₀ θ ]T) [ δ ]T ∎                        
             in (Tm Γ) ⊢ π₁ (θ ∘ δ) ≡[ aux ]≡ (π₁ θ) [ δ ]t       
    
```
Semantics
```
open import Data.Unit
open import Data.Product renaming (_,_ to _,'_)
open import Function renaming (id to id' ; _∘_ to _∘'_)

data U : Set 
El : U → Set

data U where
  ⊤U : U
  ΣU : (A : U) → (El A → U) → U 

El ⊤U = ⊤
El (ΣU A B) = Σ[ x ∈ El A ] El (B x)

open CwF

model : CwF
Con model = U
Tms model Γ Δ = El Γ → El Δ
id model = id'
_∘_ model δ γ = δ ∘' γ
idl model = refl
idr model = refl
ass model = refl
Ty model Γ = El Γ → U
_[_]T model A δ = A ∘' δ
[id]T model = refl
[∘]T model = refl
Tm model Γ A = (x : El Γ) → El (A x)
_[_]t model a δ x = a (δ x)
[id]t model = refl
[∘]t model = refl
• model = ⊤U
ε model x = tt
•-η model = refl
_▷_ model Γ A = ΣU Γ A
_,_ model γ a x = γ x ,' a x
π₀ model δ x = proj₁ (δ x)
π₁ model δ x = proj₂ (δ x)
▷-β₀ model = refl
▷-β₁ model = refl
▷-η model = refl
π₀∘ model = refl
π₁∘ model = refl
```
