module deBruijn where

open import Data.Nat.Base using (ℕ; zero; suc)

infix  5 ƛ_
infixl 7 _·_
infix  9  `_

data Ter : Set where
  `_   : ℕ → Ter
  _·_  : Ter → Ter → Ter
  ƛ_   : Ter → Ter

-- substitution type
Sub : Set
Sub = ℕ → Ter

-- identity substitution
I : Sub
I = λ n → ` n

-- successor substitution
S : Sub
S = λ n → ` suc n

-- cons operation
_∙_ : Ter → Sub → Sub
s ∙ σ = λ { zero    → s
          ; (suc n) → σ n
          }

-- instantiation operation
_[_] : Ter → Sub → Ter
-- up
⇑_ : Sub → Sub
-- composition
_∘_ : Sub → Sub → Sub

(` n)   [ σ ] = σ n
(s · t) [ σ ] = (s [ σ ]) · (t [ σ ])
(ƛ s)   [ σ ] = ƛ (s [ ⇑ σ ])

⇑ σ = (` 0) ∙ (σ ∘ S)

σ ∘ τ = λ n → (σ n) [ τ ]
