
module Reduction where

open import Data.Product as Prod
open import Data.Sum as Sum

open import Syntax
open import Substitution

-- By-name reduction relation. Has generating cases for each redex,
-- reflexivity and transitivity.
data _~>_ : Tm Γ s -> Tm Γ t -> Set where
  ca-il : {e : Tm Γ s}
       -> {l : Tm (Γ ∷ s) u}
       -> {r : Tm (Γ ∷ t) u}
       -> ca (il e) l r ~> sub e l

  ca-ir : {e : Tm Γ t}
       -> {l : Tm (Γ ∷ s) u}
       -> {r : Tm (Γ ∷ t) u}
       -> ca (ir e) l r ~> sub e r

  ca-ev : {e₀ e₁ : Tm Γ (s + t)}
       -> {l : Tm (Γ ∷ s) u}
       -> {r : Tm (Γ ∷ t) u}
       -> e₀ ~> e₁
       -> ca e₀ l r ~> ca e₁ l r

  ap-la : {e : Tm (Γ ∷ s) t}
       -> {m : Tm Γ s}
       -> ap (la e) m ~> sub m e

  ap-ev : {f₀ f₁ : Tm Γ (s ⇒ t)}
       -> {e : Tm Γ s}
       -> f₀ ~> f₁
       -> ap f₀ e ~> ap f₁ e
  
  now  : {e : Tm Γ s} -> e ~> e

  trans : {e₀ e₁ e₂ : Tm Γ s}
       -> e₀ ~> e₁ -> e₁ ~> e₂ -> e₀ ~> e₂

-- A subset of terms is admissible if it is closed under backwards
-- evaluation.
isAdmissible : (t : Ty) -> (Tm [] t -> Set) -> _
isAdmissible t P = ∀{e₀ e₁} -> e₀ ~> e₁ -> P e₁ -> P e₀

Tŷ : Ty -> Set₁
Tŷ t = Σ _ (isAdmissible t)

-- [_]T interprets types into admisible subsets of terms.
[_]T : (t : Ty) -> Tŷ t

-- ⟦ t ⟧T is the actual type of values of the subset [ t ]T
⟦_⟧T : (t : Ty) -> Set
⟦ t ⟧T = Σ _ ([ t ]T .proj₁)

[ un ]T .proj₁ m = m ~> tt
[ un ]T .proj₂ = trans

[ s ⇒ t ]T .proj₁ f = ∀((e , _) : ⟦ s ⟧T) -> [ t ]T .proj₁ (ap f e)
[ s ⇒ t ]T .proj₂ f₀₁ k e = [ t ]T .proj₂ (ap-ev f₀₁) (k e)

[ s + t ]T .proj₁ m
  = (Σ[ (n , _) ∈ ⟦ s ⟧T ] m ~> il {s = s} {t = t} n)
  ⊎ (Σ[ (n , _) ∈ ⟦ t ⟧T ] m ~> ir {t = t} {s = s} n)
[ s + t ]T .proj₂ e₀₁ (inj₁ (n , e₁l))
  = inj₁ (n , trans e₀₁ e₁l)
[ s + t ]T .proj₂ e₀₁ (inj₂ (n , e₁r))
  = inj₂ (n , trans e₀₁ e₁r)

Cx̂ : Cx -> _
Cx̂ Γ = Su [] Γ -> Set

-- [_]C interprets contexts into a subset of closed substitutions
-- Valid substitutions should have terminating values
[_]C : (Γ : Cx) -> Cx̂ Γ
[ s ]C γ = ∀{t} v -> [ t ]T .proj₁ (lookup γ v)

-- ⟦ Γ ⟧C is the actual type of values of the subset [ Γ ]C
⟦_⟧C : Cx -> Set
⟦ Γ ⟧C = Σ _ [ Γ ]C

-- Extension of terminating contexts.
_⟫_ : ⟦ Γ ⟧C -> ⟦ t ⟧T -> ⟦ Γ ∷ t ⟧C
(γ ⟫ τ) .proj₁        = γ .proj₁ ⟩ τ .proj₁
(γ ⟫ τ) .proj₂ to     = τ .proj₂
(γ ⟫ τ) .proj₂ (po v) = γ .proj₂ v

-- The semantics of of a term `e : Tm t Γ` is a mapping from `γ : ⟦ Γ ⟧C`
-- to ⟦ t ⟧T that acts as substitution by the first component of γ.
-- This can be expressed much more nicely using dependent types. Trying
-- to work with actual 'subsets' results in endless futzing with
-- identity types/'singletons'.
Sem : (Γ : Cx) -> (t : Ty) -> Tm Γ t -> Set
Sem Γ t e = ∀(γ : ⟦ Γ ⟧C) -> [ t ]T .proj₁ (ssub (proj₁ γ) e)

idx : (v : Vr Γ t) -> Sem Γ t (vr v)
idx v γ = γ .proj₂ v

-- The fold proving the fundamental theorem.
sem : ∀ Γ t (e : Tm Γ t) -> Sem Γ t e
syntax sem Γ t e = ⟦ Γ ⊢ e ∈ t ⟧

⟦ Γ ⊢ vr v ∈ s ⟧ γ = idx v γ
⟦ Γ ⊢ tt ∈ un ⟧ _ = now

⟦ Γ ⊢ la e ∈ s ⇒ t ⟧ γ z =
  [ t ]T .proj₂ ap-la (⟦ Γ ∷ s ⊢ e ∈ t ⟧ (γ ⟫ z))

⟦ Γ ⊢ ap f e ∈ t ⟧ γ = ⟦ Γ ⊢ f ∈ _ ⇒ t ⟧ γ (_ , ⟦ Γ ⊢ e ∈ _ ⟧ γ)

⟦ Γ ⊢ il e ∈ s + t ⟧ γ = inj₁ ((_ , ⟦ Γ ⊢ e ∈ s ⟧ γ) , now)
⟦ Γ ⊢ ir e ∈ s + t ⟧ γ = inj₂ ((_ , ⟦ Γ ⊢ e ∈ t ⟧ γ) , now)

⟦ Γ ⊢ ca e l r ∈ u ⟧ γ with ⟦ Γ ⊢ e ∈ _ + _ ⟧ γ
... | inj₁ (x , e~>il-x) =
  [ u ]T .proj₂ (trans (ca-ev e~>il-x) ca-il)
    (⟦ Γ ∷ _ ⊢ l ∈ u ⟧ (γ ⟫ x))
... | inj₂ (y , e~>ir-y) =
  [ u ]T .proj₂ (trans (ca-ev e~>ir-y) ca-ir)
    (⟦ Γ ∷ _ ⊢ r ∈ u ⟧ (γ ⟫ y))

termination
  : (e : Tm [] (s + t))
 -> Σ[ x ∈ Tm [] s ] (e ~> il {t = t} x)
  ⊎ Σ[ y ∈ Tm [] t ] (e ~> ir {s = s} y)
termination e with ⟦ [] ⊢ e ∈ _ + _ ⟧ (reflₛᵤ , λ())
... | inj₁ ((x , _), e~>lx) = inj₁ (x , e~>lx)
... | inj₂ ((y , _), e~>ry) = inj₂ (y , e~>ry)
