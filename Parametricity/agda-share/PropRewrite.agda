module PropRewrite where

data Ω : Set where
  ⊤ ⊥ : Ω
  _∧_ _∨_ _⊃_ : Ω → Ω → Ω

data Ctx : Set where
  [] : Ctx
  _,,_ : Ctx → Ω → Ctx

variable
  P Q R : Ω
  Γ : Ctx

data Prf : Ctx → Ω → Set where
  top : Prf (Γ ,, P) P
  pop : Prf Γ Q → Prf (Γ ,, P) Q
  tt : Prf Γ ⊤
  _,_ : Prf Γ P → Prf Γ Q → Prf Γ (P ∧ Q)
  prl : Prf Γ (P ∧ Q) → Prf Γ P
  prr : Prf Γ (P ∧ Q) → Prf Γ Q
  inl : Prf Γ P → Prf Γ (P ∨ Q)
  inr : Prf Γ Q → Prf Γ (P ∨ Q)
  cas : Prf (Γ ,, P) R → Prf (Γ ,, Q) R → Prf Γ (P ∨ Q) → Prf Γ R
  abs : Prf (Γ ,, P) Q → Prf Γ (P ⊃ Q)
  app : Prf Γ (P ⊃ Q) → Prf Γ P → Prf Γ Q

replace-prop : Ω → Ω → Ω
replace-prop P ⊤ = ⊤
replace-prop P ⊥ = P
replace-prop P (Q ∧ R) = replace-prop P Q ∧ replace-prop P R
replace-prop P (Q ∨ R) = replace-prop P Q ∨ replace-prop P R
replace-prop P (Q ⊃ R) = replace-prop P Q ⊃ replace-prop P R

replace-ctx : Ω → Ctx → Ctx
replace-ctx P [] = []
replace-ctx P (Γ ,, Q) = replace-ctx P Γ ,, replace-prop P Q

lemma : ∀ P Γ → Prf Γ Q → Prf (replace-ctx P Γ) (replace-prop P Q)
lemma P (Γ ,, ⊥) top = top
lemma P (Γ ,, _) top = top
lemma P (Γ ,, Q) (pop p) = pop (lemma P Γ p)
lemma P Γ tt = tt
lemma P Γ (p , q) = lemma P Γ p , lemma P Γ q
lemma P Γ (prl p) = prl (lemma P Γ p)
lemma P Γ (prr p) = prr (lemma P Γ p)
lemma P Γ (inl p) = inl (lemma P Γ p)
lemma P Γ (inr p) = inr (lemma P Γ p)
lemma P Γ (cas l r s) = cas (lemma P _ l) (lemma P _ r) (lemma P _ s)
lemma P Γ (abs e) = abs (lemma P (Γ ,, _) e)
lemma P Γ (app p q) = app (lemma P Γ p) (lemma P Γ q)

⊥-elim : Prf Γ ⊥ → Prf (replace-ctx P Γ) P
⊥-elim = lemma _ _
