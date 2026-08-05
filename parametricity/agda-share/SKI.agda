
module SKI where

open import Data.Nat
open import Data.Fin

infixl 30 _⟨_⟩
infixl 10 λ:_
infix  40 $_

data L : ℕ → Set where
  $_   : ∀{n} → Fin n → L n
  λ:_  : ∀{n} → L (suc n) → L n
  _⟨_⟩ : ∀{n} → L n → L n → L n

data C : Set where
  S K I : C
  _⟨_⟩  : C → C → C

weaken : ℕ → C → C
weaken zero    acc = acc
weaken (suc n) acc = weaken n (K ⟨ acc ⟩)

-- S(KS)Kgfx
-- KSg(Kg)fx
-- S(Kg)fx
-- Kgx(fx)
-- g(fx)
O : C
O = S ⟨ K ⟨ S ⟩ ⟩ ⟨ K ⟩

_∘_ : C → C → C
g ∘ f = O ⟨ g ⟩ ⟨ f ⟩

queue-index : ∀ n → Fin n → C
queue-index n k = aux n k I
 where
 aux : ∀ n → Fin n → C → C
 aux .(suc n) (zero {n})   acc = weaken n acc
 aux .(suc n) (suc  {n} k) acc = aux n k (K ∘ acc)

-- S(K(S(KS)))(S(KS)K)fghx
-- K(S(KS))f(S(KS)Kf)ghx
-- S(KS)(S(KS)Kf)ghx
-- S(KS)(KSf(Kf))ghx
-- S(KS)(S(Kf))ghx
-- KSg(S(Kf)g)hx
-- S(S(Kf)g)hx
-- S(Kf)gx(hx)
-- Kfx(gx)(hx)
-- f(gx)(hx)
F : C
F = S ⟨ K ⟨ S ⟨ K ⟨ S ⟩ ⟩ ⟩ ⟩ ⟨ S ⟨ K ⟨ S ⟩ ⟩ ⟨ K ⟩ ⟩

-- F(Ff)ghxy
-- (Ff)(gx)(hx)y
-- f(gxy)(hxy)

fork : ℕ → C → C
fork zero    acc = acc
fork (suc n) acc = fork n (F ⟨ acc ⟩)

compile : ∀{n} → L n → C
compile ($ k)         = queue-index _ k
compile (λ: e)        = compile e
compile {n} (f ⟨ x ⟩) = fork n I ⟨ compile f ⟩ ⟨ compile x ⟩

T : Set
T = L 0

id : T
id = λ: $ zero

const : T
const = λ: λ: $ suc zero
-- S(KS)KKI
-- KSK(KK)I
-- S(KK)I
-- 
-- S(KK)Ixy
-- KKx(Ix)y
-- Kxy
-- x

const₂ : T
const₂ = λ: λ: $ zero
-- KIxy
-- Iy
-- y

ω : T
ω = (λ: ($ zero) ⟨ $ zero ⟩) ⟨ λ: ($ zero) ⟨ $ zero ⟩ ⟩

reduce₁ : C → C
reduce₁ (I ⟨ x ⟩)             = reduce₁ x
reduce₁ (S ⟨ f ⟩ ⟨ g ⟩ ⟨ x ⟩) =
  reduce₁ f ⟨ reduce₁ x ⟩ ⟨ reduce₁ g ⟨ reduce₁ x ⟩ ⟩
reduce₁ (K ⟨ x ⟩ ⟨ y ⟩)       = reduce₁ x
reduce₁ (f ⟨ x ⟩)             = reduce₁ f ⟨ reduce₁ x ⟩
reduce₁ e                     = e

reduce : ℕ → C → C
reduce zero    e = e
reduce (suc n) e = reduce n (reduce₁ e)

