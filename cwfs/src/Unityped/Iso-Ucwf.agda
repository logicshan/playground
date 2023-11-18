module Unityped.Iso-Ucwf where

open import Data.Nat hiding (_/_) renaming (ℕ to Nat)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec hiding ([_] ; lookup)
open import Relation.Binary
open import Function using (_$_ ; _∘_)
open import Relation.Binary.PropositionalEquality as P hiding ([_])
import Relation.Binary.Reasoning.Setoid as EqR

open import Unityped.Ucwf
open import Unityped.ExpSub renaming (q to q⋆ ; p to p⋆ ; id to id⋆ ; _∙_ to _∙⋆_)
open import Unityped.ImpSub hiding (p⋆ ; subComp ; compExt ; left-zero ; idExt ; p-∙ ; lookup)

⟦_⟧  : ∀ {n} → Tm n → Fin n
⟦_⟧' : ∀ {m n} → Sub m n → Ren m n

⟦ q⋆ ⟧      = zero
⟦ t [ ρ ] ⟧ = ⟦ t ⟧ / ⟦ ρ ⟧'

⟦ id⋆ ⟧'       = id
⟦ p⋆  ⟧'       = p
⟦ <>  ⟧'       = []
⟦ ρ₁ ∙⋆ ρ₂  ⟧' = ⟦ ρ₁ ⟧' ∙ ⟦ ρ₂ ⟧'
⟦ < ρ , t > ⟧' = ⟦ t ⟧ ∷ ⟦ ρ ⟧'

varExp : ∀ {n} (i : Fin n) → Tm n
varExp zero    = q⋆
varExp (suc i) = varExp i [ p⋆ ]

⟪_⟫  : ∀ {n} → Fin n → Tm n
⟪_⟫' : ∀ {m n} → Ren m n → Sub m n

⟪ i ⟫ = varExp i

⟪ [] ⟫'    = <>
⟪ i ∷ ρ ⟫' = < ⟪ ρ ⟫' , ⟪ i ⟫ >

ExpSubUcwf⇒ : Ucwf-⇒ ExpSubUcwf ImpSubUcwf
ExpSubUcwf⇒ = record
                { ⟦_⟧           = ⟦_⟧
                ; ⟦_⟧'          = ⟦_⟧'
                ; id-preserved  = refl
                ; q-preserved   = refl
                ; p-preserved   = refl
                ; ∘-preserved   = λ _ _ → refl
                ; <>-preserved  = refl
                ; <,>-preserved = λ _ _ → refl
                ; sub-preserved = λ _ _ → refl
                }

module Proj where

  varsExp : ∀ {m n} → Ren m n → Sub m n
  varsExp []      = <>
  varsExp (i ∷ ρ) = < varsExp ρ , varExp i >

  var-lemma : ∀ {m n} (ρ : Ren m n) → varsExp ρ ∙⋆ p⋆ ≈ varsExp (map suc ρ)
  var-lemma []      = left-zero
  var-lemma (i ∷ ρ) = begin
    < varsExp ρ , varExp i > ∙⋆ p⋆            ≈⟨ compExt ⟩
    < varsExp ρ ∙⋆ p⋆ , varExp i [ p⋆ ] >     ≈⟨ cong-<, (var-lemma ρ) ⟩
    < varsExp (map suc ρ) , varExp i [ p⋆ ] >
    ∎
    where open EqR (SubSetoid {_} {_})

  p⋆-norm : ∀ {n} → Sub (suc n) n
  p⋆-norm {n} = varsExp p

  p⋆≈p⋆-norm : ∀ {n} → p⋆ {n} ≈ varsExp p
  p⋆≈p⋆-norm {zero}  = emptySub _
  p⋆≈p⋆-norm {suc n} = begin
    p⋆                                  ≈⟨ surj-<,> p⋆ ⟩
    < p⋆ ∙⋆ p⋆ , q⋆ [ p⋆ ] >            ≈⟨ cong-<, (cong-∙₁ p⋆≈p⋆-norm) ⟩
    < varsExp p ∙⋆ p⋆ , q⋆ [ p⋆ ] >     ≈⟨ cong-<, (var-lemma p) ⟩
    < varsExp (map suc p) , q⋆ [ p⋆ ] > 
    ∎
    where open EqR (SubSetoid {_} {_})

  vars-any : ∀ {m n} (ρ : Ren m n) → ⟪ ρ ⟫' ≈ varsExp ρ
  vars-any []      = refl≈
  vars-any (_ ∷ ρ) = cong-<, (vars-any ρ)

  vars-p : ∀ {n} → ⟪ p {n} ⟫' ≈ varsExp p
  vars-p = vars-any p

p-preserved : ∀ {n} → ⟪ p {n} ⟫' ≈ p⋆
p-preserved = trans≈ Proj.vars-p (sym≈ $ Proj.p⋆≈p⋆-norm)

id-preserved : ∀ {n} → ⟪ id {n} ⟫' ≈ id⋆
id-preserved {zero}  = sym≈ id-zero
id-preserved {suc n} = begin
  < ⟪ p ⟫' , ⟪ zero ⟫ > ≈⟨ cong-<, p-preserved ⟩
  < p⋆ , q⋆ >           ≈⟨ sym≈ idExt ⟩
  id⋆
  ∎
  where open EqR (SubSetoid {_} {_})

sub-preserved : ∀ {m n} (i : Fin n) (ρ : Ren m n) → ⟪ i / ρ ⟫ ~ ⟪ i ⟫ [ ⟪ ρ ⟫' ]
sub-preserved zero    (_ ∷ _) = sym~ q-sub
sub-preserved (suc i) (j ∷ ρ) = begin
  ⟪ i / ρ ⟫                           ≈⟨ sub-preserved i ρ ⟩
  ⟪ i ⟫ [ ⟪ ρ ⟫' ]                    ≈⟨ cong-sub₂ (sym≈ p-∙) ⟩
  ⟪ i ⟫ [ p⋆ ∙⋆ < ⟪ ρ ⟫' , ⟪ j ⟫ > ]  ≈⟨ subComp ⟩
  ⟪ i ⟫ [ p⋆ ] [ < ⟪ ρ ⟫' , ⟪ j ⟫ > ]
  ∎
  where open EqR (TmSetoid {_})

∙-preserved : ∀ {m n k} (ρ₁ : Ren k n) (ρ₂ : Ren m k) → ⟪ ρ₁ ∙ ρ₂ ⟫' ≈ ⟪ ρ₁ ⟫' ∙⋆ ⟪ ρ₂ ⟫'
∙-preserved [] ρ₂ = sym≈ left-zero
∙-preserved (i ∷ ρ₁) ρ₂ = begin
  < ⟪ ρ₁ ∙ ρ₂ ⟫' , ⟪ i / ρ₂ ⟫ >              ≈⟨ cong-<, (∙-preserved ρ₁ ρ₂) ⟩
  < ⟪ ρ₁ ⟫' ∙⋆ ⟪ ρ₂ ⟫' , ⟪ i / ρ₂ ⟫ >        ≈⟨ cong-,> (sub-preserved i ρ₂) ⟩
  < ⟪ ρ₁ ⟫' ∙⋆ ⟪ ρ₂ ⟫' , ⟪ i ⟫ [ ⟪ ρ₂ ⟫' ] > ≈⟨ sym≈ compExt ⟩
  < ⟪ ρ₁ ⟫' , ⟪ i ⟫ > ∙⋆ ⟪ ρ₂ ⟫'
  ∎
  where open EqR (SubSetoid {_} {_})

ImpSubUcwf⇒ : Ucwf-⇒ ImpSubUcwf ExpSubUcwf
ImpSubUcwf⇒ = record
                { ⟦_⟧           = ⟪_⟫
                ; ⟦_⟧'          = ⟪_⟫'
                ; id-preserved  = id-preserved
                ; q-preserved   = refl~
                ; p-preserved   = p-preserved
                ; ∘-preserved   = ∙-preserved
                ; <>-preserved  = refl≈
                ; <,>-preserved = λ _ _ → refl≈
                ; sub-preserved = sub-preserved
                }

left-inv-tm : ∀ {n} (t : Tm n) → ⟪ ⟦ t ⟧ ⟫ ~ t

left-inv-sub : ∀ {m n} (ρ : Sub m n) → ⟪ ⟦ ρ ⟧' ⟫' ≈ ρ
left-inv-sub id⋆        = id-preserved
left-inv-sub p⋆         = p-preserved
left-inv-sub <>         = refl≈
left-inv-sub < ρ , t >  = cong-<,> (left-inv-tm t) (left-inv-sub ρ)
left-inv-sub (ρ₁ ∙⋆ ρ₂) = begin
  ⟪ ⟦ ρ₁ ⟧' ∙ ⟦ ρ₂ ⟧' ⟫'       ≈⟨ ∙-preserved ⟦ ρ₁ ⟧' ⟦ ρ₂ ⟧' ⟩
  ⟪ ⟦ ρ₁ ⟧' ⟫' ∙⋆ ⟪ ⟦ ρ₂ ⟧' ⟫' ≈⟨ cong-∙₁ (left-inv-sub ρ₁) ⟩
  ρ₁ ∙⋆ ⟪ ⟦ ρ₂ ⟧' ⟫'           ≈⟨ cong-∙₂ (left-inv-sub ρ₂) ⟩
  ρ₁ ∙⋆ ρ₂
  ∎
  where open EqR (SubSetoid {_} {_})

left-inv-tm q⋆        = refl~
left-inv-tm (t [ ρ ]) = begin
  ⟪ ⟦ t ⟧ / ⟦ ρ ⟧' ⟫        ≈⟨ sub-preserved ⟦ t ⟧ ⟦ ρ ⟧' ⟩
  ⟪ ⟦ t ⟧ ⟫ [ ⟪ ⟦ ρ ⟧' ⟫' ] ≈⟨ cong-sub₁ (left-inv-tm t) ⟩
  t [ ⟪ ⟦ ρ ⟧' ⟫' ]         ≈⟨ cong-sub₂ (left-inv-sub ρ) ⟩
  t [ ρ ]
  ∎
  where open EqR (TmSetoid {_})

right-inv-tm : ∀ {n} (i : Fin n) → ⟦ ⟪ i ⟫ ⟧ ≡ i
right-inv-tm zero    = refl
right-inv-tm (suc i) = begin
  ⟦ ⟪ suc i ⟫ ⟧ ≡⟨⟩
  ⟦ ⟪ i ⟫ ⟧ / p ≡⟨ cong (_/ p) (right-inv-tm i) ⟩
  i / p         ≡⟨ lookup-p i ⟩
  suc i
  ∎
  where open P.≡-Reasoning

right-inv-sub : ∀ {m n} (ρ : Vec (Fin m) n) → ⟦ ⟪ ρ ⟫' ⟧' ≡ ρ
right-inv-sub []      = refl
right-inv-sub (i ∷ ρ) = cong₂ _∷_ (right-inv-tm i) (right-inv-sub ρ)

ExpSub≅ImpSub : Ucwf-≅ ExpSubUcwf⇒ ImpSubUcwf⇒
ExpSub≅ImpSub = record
                  { left-inv-tm   = left-inv-tm
                  ; right-inv-tm  = right-inv-tm
                  ; left-inv-sub  = left-inv-sub
                  ; right-inv-sub = right-inv-sub
                  }
