To compare with combinatory logic we define weak untyped lambda calculus.

Basically the complexity is very similar, but we have to introduce
environments and closures. 

```
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

infixl 20 _$_

variable m n : ℕ

data Tm : ℕ → Set where
  zero : Tm (suc n)
  suc : Tm n → Tm (suc n)
  _$_ : Tm n → Tm n → Tm n
  ƛ : Tm (suc n) → Tm n

variable t t' u u' : Tm n

data Clos : Set
data Env : ℕ → Set where
  ε : Env 0
  _,_ : Clos → Env n → Env (suc n)

variable ρ ρ' : Env n

data Val : Set where
  ƛv_[_] : Tm (suc n) → Env n →  Val

variable v v' w w' : Val

data Clos where
  _[_] : Tm n → Env n → Clos

variable c c' d d' : Clos

clos : Tm 0 → Clos
clos t = t [ ε ]

infix 5 _↓_

data _↓_ : Clos → Val → Set where
  zero : c ↓ v 
       → zero [ c , ρ ] ↓ v 
  suc : t [ ρ ] ↓ v 
       → (suc t) [ c , ρ ] ↓ v 
  ƛ : (ƛ t) [ ρ ] ↓ ƛv t [ ρ ]
  app : t [ ρ ] ↓ ƛv t' [ ρ' ]
      → t' [ u [ ρ ] , ρ' ] ↓ v
      → (t $ u) [ ρ ] ↓ v

I : Tm n
I = ƛ zero

ω : Tm n
ω = ƛ (zero $ zero)

```

```
det-↓ : c ↓ v → c ↓ v' → v ≡ v'
det-↓ (zero r) (zero s) = det-↓ r s
det-↓ (suc r) (suc s) = det-↓ r s
det-↓ ƛ ƛ = refl
det-↓ (app r r') (app s s') with det-↓ r s
... | refl = det-↓ r' s'
```

```
infix 5 _⊑_ _~_

_⊑_ : Clos → Clos → Set
c ⊑ d = ∀ {v} → (c ↓ v) → (d ↓ v)

refl-⊑ : c ⊑ c
refl-⊑ x = x

trans-⊑ : c ⊑ d → d ⊑ d' → c ⊑ d'
trans-⊑ f g x = g (f x)

_~_ : Clos → Clos → Set
c ~ d = c ⊑ d × d ⊑ c

~-setoid : Setoid _ _
~-setoid = record { Carrier = Clos ; _≈_ = _~_ ;
                    isEquivalence = record {
                      refl = refl-⊑ , refl-⊑ ;
                      sym = λ (p , p') → p' , p ;
                      trans = λ (p , p') (q , q')
                                   → (trans-⊑ p q) , (trans-⊑ q' p') } }
```

We need to define all relations on closures not on closed terms!
```
open import Relation.Binary.Reasoning.Setoid ~-setoid

$-lem : (t [ ρ ]) ⊑ (t' [ ρ ]) → (t $ u) [ ρ ] ⊑ (t' $ u)[ ρ ]
$-lem h (app g r) = app (h g) r

$-prop : (t [ ρ ]) ~ (t' [ ρ ]) → (t $ u) [ ρ ] ~ (t' $ u)[ ρ ]
$-prop (p , p') = ($-lem p) , ($-lem p')

I-prop : (I $ t)[ ρ ] ~ t [ ρ ]
proj₁ I-prop (app ƛ (zero g)) = g
proj₂ I-prop h = app ƛ (zero h)

ω-prop : (ω $ t) [ ρ ] ~ (suc t $ zero)[ t [ ρ ] , ρ ]
proj₁ ω-prop (app ƛ (app (zero h₁) h₂)) = app (suc h₁) h₂
proj₂ ω-prop (app (suc g₁) g₂) = app ƛ (app (zero g₁) g₂)
```

```
Ω : Tm n
Ω = ω $ ω

ω-nf : Val
ω-nf = (ƛv (zero $ zero) [ ε ])
  
thm : clos Ω ↓ w' → ⊥
thm (app ƛ r₁) = loop ƛ r₁
  where loop : c ↓ ω-nf → zero $ zero [ c , ε ] ↓ v → ⊥
        loop r (app (zero s) s₁) with det-↓ r s
        ... | refl = loop (zero r) s₁


```
