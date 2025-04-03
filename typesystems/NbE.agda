{-# OPTIONS --prop --rewriting #-}
module NbE where

open import Lib

import Def.Syntax
import Def.DepModel
open import Def.Model
import Def.ParaModel

St : Model
St = record
  { Ty        = Set
  ; Nat       = ℕ
  ; Bool      = 𝟚
  ; Con       = Set
  ; ◇         = Lift ⊤
  ; _▹_       = _×_
  ; Var       = λ Γ A → Γ → A
  ; vz        = π₂
  ; vs        = λ σ → σ ∘ π₁
  ; Tm        = λ Γ A → Γ → A
  ; Sub       = λ Δ Γ → Δ → Γ
  ; p         = π₁
  ; ⟨_⟩       = λ t γ → (γ , t γ)
  ; _⁺        = λ σ δa → σ (π₁ δa) , π₂ δa
  ; var       = λ x → x
  ; _[_]      = λ t σ → t ∘ σ
  ; [p]       = refl
  ; vz[⟨⟩]    = refl
  ; vz[⁺]     = refl
  ; vs[⟨⟩]    = refl
  ; vs[⁺]     = refl
  ; true      = λ _ → tt
  ; false     = λ _ → ff
  ; ite       = λ t u v γ → if t γ then u γ else v γ
  ; iteβ₁     = refl
  ; iteβ₂     = refl
  ; true[]    = refl
  ; false[]   = refl
  ; ite[]     = refl
  ; num       = λ n _ → n
  ; isZero    = λ t γ → iteℕ tt (λ _ → ff) (t γ)
  ; _+o_      = λ u v γ → u γ + v γ
  ; isZeroβ₁  = refl
  ; isZeroβ₂  = refl
  ; +β        = refl
  ; num[]     = refl
  ; isZero[]  = refl
  ; +[]       = refl
  }
module St = Model St

import Def.Syntax as I

not-equal : ¬ (
  I.ite (I.isZero (I.num 2)) (I.num 3) (I.num 12) ≡
  I.ite (I.isZero (I.num 0 I.+o I.num 0)) (I.num 11) (I.num {I.◇} 3))
not-equal e = 12≠11 (cong (λ t → St.⟦ t ⟧t (mk triv)) e)
  where
    12≠11 : ¬ (12 ≡ 11)
    12≠11 ()

ex-open : St.⟦ I.isZero (I.var (I.vz {I.◇}) I.+o I.num 2) ⟧t ≡ St.⟦ I.false {I.◇ I.▹ I.Nat} ⟧t
ex-open = funext λ { (_ , n) → cong (iteℕ tt (λ _ → ff)) (+comm {n}{2}) }

data _hasLength_ : I.Con → ℕ → Set where
  nil   : I.◇ hasLength 0
  snoc  : ∀{Γ n} → Γ hasLength n → (A : I.Ty) → (Γ I.▹ A) hasLength suc n

import DefABT

Inf : DefABT.Model
Inf = record
        { Var = λ n → {Γ : I.Con} → Γ hasLength n → Σ I.Ty λ A → I.Var Γ A
        ; vz = λ { (snoc _ A) → A , I.vz }
        ; vs = λ { infx (snoc Γn A) → π₁ (infx Γn) , I.vs (π₂ (infx Γn))  }
        ; Tm = λ n → {Γ : I.Con} → Γ hasLength n → Maybe (Σ I.Ty λ A → I.Tm Γ A)
        ; var = λ infx Γn → just (π₁ (infx Γn) , I.var (π₂ (infx Γn)))
        ; def = def
        ; true = λ _ → just (I.Bool , I.true)
        ; false = λ _ → just (I.Bool , I.false)
        ; ite = ite
        ; num = λ n _ → just (I.Nat , I.num n)
        ; isZero = isZero
        ; _+o_ = _+o_
        }
  where
    def : ∀{n} →  (∀{Γ}  → Γ hasLength n      → Maybe (Σ I.Ty (I.Tm Γ))) →
                  (∀{Γ}  → Γ hasLength suc n  → Maybe (Σ I.Ty (I.Tm Γ))) →
                  ∀{Γ}   → Γ hasLength n      → Maybe (Σ I.Ty (I.Tm Γ))
    def infu inft Γn with infu Γn
    ... | nothing = nothing
    ... | just (A , u) with inft (snoc Γn A)
    ... | nothing = nothing
    ... | just (B , t) = just (B , t I.[ I.⟨ u ⟩ ])

    ite : ∀{n} →  (∀{Γ}  → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))) →
                  (∀{Γ}  → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))) →
                  (∀{Γ}  → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))) →
                  ∀{Γ}   → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))
    ite inft infu infv Γn with inft Γn | infu Γn | infv Γn
    ... | just (I.Bool , t)  | just (I.Bool  , u)  | just (I.Bool  , v)  = just (I.Bool  , I.ite t u v)
    ... | just (I.Bool , t)  | just (I.Nat   , u)  | just (I.Nat   , v)  = just (I.Nat   , I.ite t u v)
    ... | _                  | _                   | _                   = nothing

    isZero : ∀{n} →  (∀{Γ}  → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))) →
                     ∀{Γ}   → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))
    isZero inft Γn with inft Γn
    ... | just (I.Nat , t)  = just (I.Bool , I.isZero t)
    ... | _                 = nothing

    _+o_ : ∀{n} →  (∀{Γ}  → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))) →
                   (∀{Γ}  → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))) →
                   ∀{Γ}   → Γ hasLength n → Maybe (Σ I.Ty (I.Tm Γ))
    _+o_ infu infv Γn with infu Γn | infv Γn
    ... |  just (I.Nat , u) |  just (I.Nat , v)  = just (I.Nat , u I.+o v)
    ... |  _                |  _                 = nothing
module Inf = DefABT.Model Inf

infer : DefABT.I.Tm 0 → Maybe (Σ I.Ty λ A → I.Tm I.◇ A)
infer pt = Inf.⟦ pt ⟧t nil

open I

infixl 6 _[_]V _[_]Ne _[_]Nf
infixl 7 _+NeNe_ _+NeNf_ _+NfNe_ _+NfNf_

data Ne (Γ : Con) : Ty → Set
data Nf (Γ : Con) : Ty → Set

data Ne Γ where
  varNe     : ∀{A} → Var Γ A → Ne Γ A
  iteNe     : ∀{A} → Ne Γ Bool → Nf Γ A → Nf Γ A → Ne Γ A
  isZeroNe  : Ne Γ Nat → Ne Γ Bool
  _+NeNe_   : Ne Γ Nat → Ne Γ Nat → Ne Γ Nat
  _+NeNf_   : Ne Γ Nat → ℕ → Ne Γ Nat
  _+NfNe_   : ℕ → Ne Γ Nat → Ne Γ Nat

data Nf Γ where
  neu       : ∀{A} → Ne Γ A → Nf Γ A
  trueNf    : Nf Γ Bool
  falseNf   : Nf Γ Bool
  numNf     : ℕ → Nf Γ Nat

⌜_⌝Ne : ∀{Γ A} → Ne Γ A → Tm Γ A
⌜_⌝Nf : ∀{Γ A} → Nf Γ A → Tm Γ A
⌜ varNe x ⌝Ne = var x
⌜ iteNe t a a' ⌝Ne = ite ⌜ t ⌝Ne ⌜ a ⌝Nf ⌜ a' ⌝Nf
⌜ isZeroNe t ⌝Ne = isZero ⌜ t ⌝Ne
⌜ t +NeNe t' ⌝Ne = ⌜ t ⌝Ne +o ⌜ t' ⌝Ne
⌜ t +NeNf n' ⌝Ne = ⌜ t ⌝Ne +o num n'
⌜ n +NfNe t' ⌝Ne = num n +o ⌜ t' ⌝Ne
⌜ neu t ⌝Nf = ⌜ t ⌝Ne
⌜ trueNf ⌝Nf = true
⌜ falseNf ⌝Nf = false
⌜ numNf n ⌝Nf = num n

t1 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ v0 +o (num 1 +o num 2)
t2 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ v0 +o v0
t3 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ (num 1 +o num 2) +o v0
t4 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ (num 1 +o v0) +o v0
t5 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ isZero (num 2)
t6 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ isZero (num 1 +o num 2)
t7 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ isZero (num 1 +o v0)
t8 : Σsp (Nf ◇ Bool) λ v → ⌜ v ⌝Nf ≡ def (num 0) (def (isZero v0) (ite v0 false true))

t1 = exercise
t2 = exercise
t3 = exercise
t4 = exercise
t5 = exercise
t6 = exercise
t7 = exercise
t8 = exercise


data Wk  : Con → Con → Set where
  p      : ∀{Γ A} → Wk (Γ ▹ A) Γ
  _⁺Wk   : ∀{Γ Δ A} → Wk Δ Γ → Wk (Δ ▹ A) (Γ ▹ A)

data Sub1  : Con → Con → Set where
  ⟨_⟩Sub1  : ∀{Γ A} → Nf Γ A → Sub1 Γ (Γ ▹ A)
  _⁺Sub1   : ∀{Γ Δ A} → Sub1 Δ Γ → Sub1 (Δ ▹ A) (Γ ▹ A)

⌜_⌝Wk : ∀{Δ Γ} → Wk Δ Γ → Sub Δ Γ
⌜ p      ⌝Wk = p
⌜ σ ⁺Wk  ⌝Wk = ⌜ σ ⌝Wk ⁺

⌜_⌝Sub1 : ∀{Δ Γ} → Sub1 Δ Γ → Sub Δ Γ
⌜ ⟨ t ⟩Sub1  ⌝Sub1 = ⟨ ⌜ t ⌝Nf ⟩
⌜ σ ⁺Sub1    ⌝Sub1 = ⌜ σ ⌝Sub1 ⁺

iteNf : ∀{Γ A} → Nf Γ Bool → Nf Γ A → Nf Γ A → Nf Γ A
iteNf (neu t) a a' = neu (iteNe t a a')
iteNf trueNf a a' = a
iteNf falseNf a a' = a'

_+NfNf_ : ∀{Γ} → Nf Γ Nat → Nf Γ Nat → Nf Γ Nat
neu tn +NfNf neu tn' = neu (tn +NeNe tn')
neu tn +NfNf numNf n = neu (tn +NeNf n)
numNf n +NfNf neu tn = neu (n +NfNe tn)
numNf n +NfNf numNf n' = numNf (n + n')

isZeroNf : ∀{Γ} → Nf Γ Nat → Nf Γ Bool
isZeroNf (neu n) = neu (isZeroNe n)
isZeroNf (numNf zero) = trueNf
isZeroNf (numNf (suc n)) = falseNf

_[_]VWk : ∀{Γ A} → Var Γ A → ∀{Δ} → Wk Δ Γ → Var Δ A
x     [ p      ]VWk = vs x
vz    [ σ ⁺Wk  ]VWk = vz
vs x  [ σ ⁺Wk  ]VWk = vs (x [ σ ]VWk)

_[_]NeWk : ∀{Γ A} → Ne Γ A → ∀{Δ} → Wk Δ Γ → Ne Δ A
_[_]NfWk : ∀{Γ A} → Nf Γ A → ∀{Δ} → Wk Δ Γ → Nf Δ A

varNe x       [ σ ]NeWk = varNe (x [ σ ]VWk)
iteNe t u v   [ σ ]NeWk = iteNe (t [ σ ]NeWk) (u [ σ ]NfWk) (v [ σ ]NfWk)
isZeroNe t    [ σ ]NeWk = isZeroNe (t [ σ ]NeWk)
(t +NeNe t')  [ σ ]NeWk = t [ σ ]NeWk +NeNe t' [ σ ]NeWk
(t +NeNf n')  [ σ ]NeWk = t [ σ ]NeWk +NeNf n'
(n +NfNe t')  [ σ ]NeWk = n           +NfNe t' [ σ ]NeWk

neu x    [ σ ]NfWk = neu (x [ σ ]NeWk)
trueNf   [ σ ]NfWk = trueNf
falseNf  [ σ ]NfWk = falseNf
numNf n  [ σ ]NfWk = numNf n

_[_]VSub1 : ∀{Γ A} → Var Γ A → ∀{Δ} → Sub1 Δ Γ → Nf Δ A
vz    [ ⟨ t ⟩Sub1  ]VSub1 = t
vs x  [ ⟨ t ⟩Sub1  ]VSub1 = neu (varNe x)
vz    [ σ ⁺Sub1    ]VSub1 = neu (varNe vz)
vs x  [ σ ⁺Sub1    ]VSub1 = x [ σ ]VSub1 [ p ]NfWk

_[_]NeSub1 : ∀{Γ A} → Ne Γ A → ∀{Δ} → Sub1 Δ Γ → Nf Δ A
_[_]NfSub1 : ∀{Γ A} → Nf Γ A → ∀{Δ} → Sub1 Δ Γ → Nf Δ A

varNe x       [ σ ]NeSub1 = x [ σ ]VSub1
iteNe t u v   [ σ ]NeSub1 = iteNf (t [ σ ]NeSub1) (u [ σ ]NfSub1) (v [ σ ]NfSub1)
isZeroNe t    [ σ ]NeSub1 = isZeroNf (t [ σ ]NeSub1)
(t +NeNe t')  [ σ ]NeSub1 = t [ σ ]NeSub1 +NfNf t' [ σ ]NeSub1
(t +NeNf n')  [ σ ]NeSub1 = t [ σ ]NeSub1 +NfNf numNf n'
(n +NfNe t')  [ σ ]NeSub1 = numNf n       +NfNf t' [ σ ]NeSub1

neu x    [ σ ]NfSub1 = x [ σ ]NeSub1
trueNf   [ σ ]NfSub1 = trueNf
falseNf  [ σ ]NfSub1 = falseNf
numNf n  [ σ ]NfSub1 = numNf n

SubNf : Con → Con → Set
SubNf Δ Γ = Wk Δ Γ ⊎ Sub1 Δ Γ

⌜_⌝SubNf : ∀{Δ Γ} → SubNf Δ Γ → Sub Δ Γ
⌜ ι₁ σ ⌝SubNf = ⌜ σ ⌝Wk
⌜ ι₂ σ ⌝SubNf = ⌜ σ ⌝Sub1

pNf : ∀{Γ A} → SubNf (Γ ▹ A) Γ
pNf = ι₁ p

⟨_⟩Nf : ∀{Γ A} → Nf Γ A → SubNf Γ (Γ ▹ A)
⟨ t ⟩Nf = ι₂ ⟨ t ⟩Sub1

_⁺Nf : ∀{Δ Γ A} → SubNf Δ Γ → SubNf (Δ ▹ A) (Γ ▹ A)
ι₁ σ ⁺Nf = ι₁ (σ ⁺Wk)
ι₂ σ ⁺Nf = ι₂ (σ ⁺Sub1)

_[_]V : ∀{Γ A} → Var Γ A → ∀{Δ} → SubNf Δ Γ → Nf Δ A
x [ ι₁ σ ]V = neu (varNe (x [ σ ]VWk))
x [ ι₂ σ ]V = x [ σ ]VSub1

_[_]Ne : ∀{Γ A} → Ne Γ A → ∀{Δ} → SubNf Δ Γ → Nf Δ A
t [ ι₁ σ ]Ne = neu (t [ σ ]NeWk)
t [ ι₂ σ ]Ne = t [ σ ]NeSub1

_[_]Nf : ∀{Γ A} → Nf Γ A → ∀{Δ} → SubNf Δ Γ → Nf Δ A
t [ ι₁ σ ]Nf = t [ σ ]NfWk
t [ ι₂ σ ]Nf = t [ σ ]NfSub1

vz[⁺]Nf     :  ∀{Γ Δ A σ} → neu (varNe (vz {Γ}{A})) [ σ ⁺Nf ]Nf ≡ neu (varNe (vz {Δ}{A}))
vs[⁺]Nf     :  ∀{Γ Δ A B x σ} →
               neu (varNe (vs {Γ}{A}{B} x)) [ σ ⁺Nf ]Nf ≡ neu (varNe x) [ σ ]Nf [ pNf {Δ} ]Nf
true[]Nf    :  ∀{Γ Δ}{σ : SubNf Δ Γ} → trueNf [ σ ]Nf ≡ trueNf
false[]Nf   :  ∀{Γ Δ}{σ : SubNf Δ Γ} → falseNf [ σ ]Nf ≡ falseNf
ite[]Nf     :  ∀{Γ Δ A}{σ : SubNf Δ Γ}{t u v} →
               iteNf {A = A} t u v [ σ ]Nf ≡ iteNf (t [ σ ]Nf) (u [ σ ]Nf) (v [ σ ]Nf)
num[]Nf     :  ∀{Γ Δ}{σ : SubNf Δ Γ}{n} → numNf n [ σ ]Nf ≡ numNf n
isZero[]Nf  :  ∀{Γ Δ}{σ : SubNf Δ Γ}{t} → isZeroNf t [ σ ]Nf ≡ isZeroNf (t [ σ ]Nf)
+[]Nf       :  ∀{Γ Δ}{σ : SubNf Δ Γ}{u v} →
               (u +NfNf v) [ σ ]Nf ≡ (u [ σ ]Nf) +NfNf (v [ σ ]Nf)

vz[⁺]Nf {σ = ι₁ σ} = refl
vz[⁺]Nf {σ = ι₂ σ} = refl

vs[⁺]Nf {σ = ι₁ σ} = refl
vs[⁺]Nf {σ = ι₂ σ} = refl

true[]Nf {σ = ι₁ σ} = refl
true[]Nf {σ = ι₂ σ} = refl

false[]Nf {σ = ι₁ σ} = refl
false[]Nf {σ = ι₂ σ} = refl

ite[]Nf {σ = ι₁ σ} {t = neu n} = refl
ite[]Nf {σ = ι₁ σ} {t = trueNf} = refl
ite[]Nf {σ = ι₁ σ} {t = falseNf} = refl
ite[]Nf {σ = ι₂ σ} {t = neu n} = refl
ite[]Nf {σ = ι₂ σ} {t = trueNf} = refl
ite[]Nf {σ = ι₂ σ} {t = falseNf} = refl

num[]Nf {σ = ι₁ σ} = refl
num[]Nf {σ = ι₂ σ} = refl

isZero[]Nf {σ = ι₁ σ} {t = neu n} = refl
isZero[]Nf {σ = ι₁ σ} {t = numNf zero} = refl
isZero[]Nf {σ = ι₁ σ} {t = numNf (suc n)} = refl
isZero[]Nf {σ = ι₂ σ} {t = neu n} = refl
isZero[]Nf {σ = ι₂ σ} {t = numNf zero} = refl
isZero[]Nf {σ = ι₂ σ} {t = numNf (suc n)} = refl

+[]Nf {σ = ι₁ _} {u = neu _} {v = neu   _} = refl
+[]Nf {σ = ι₁ _} {u = neu _} {v = numNf _} = refl
+[]Nf {σ = ι₁ _} {u = numNf _} {v = neu _} = refl
+[]Nf {σ = ι₁ _} {u = numNf _} {v = numNf _} = refl
+[]Nf {σ = ι₂ _} {u = neu _} {v = neu _} = refl
+[]Nf {σ = ι₂ _} {u = neu _} {v = numNf _} = refl
+[]Nf {σ = ι₂ _} {u = numNf _} {v = neu _} = refl
+[]Nf {σ = ι₂ _} {u = numNf _} {v = numNf _} = refl

open import Def.ParaModel
N : ParaModel
N = record
  { Ty∙ = Lift ⊤
  ; Nat∙ = mk triv
  ; Bool∙ = mk triv
  ; Con∙ = Lift ⊤
  ; ◇∙ = _
  ; _▹∙_ = _
  ; Var∙ = λ _ _ → Lift ⊤
  ; vz∙ = _
  ; vs∙ = _
  ; Tm∙ = λ Γ A → Nf (π₁ Γ) (π₁ A)
  ; Sub∙ = λ Δ Γ → SubNf (π₁ Δ) (π₁ Γ)
  ; p∙ = pNf
  ; ⟨_⟩∙ = λ t → ⟨ π₂ t ⟩Nf
  ; _⁺∙ = λ σ → π₂ σ ⁺Nf
  ; var∙ = λ x → neu (varNe (π₁ x))
  ; _[_]∙ = λ t σ → π₂ t [ π₂ σ ]Nf
  ; [p]∙ = refl
  ; vz[⟨⟩]∙ = refl
  ; vz[⁺]∙ = λ where {σ = σ} → vz[⁺]Nf {σ = π₂ σ}
  ; vs[⟨⟩]∙ = refl
  ; vs[⁺]∙ = λ where {σ = σ} → vs[⁺]Nf {σ = π₂ σ}
  ; true∙ = trueNf
  ; false∙ = falseNf
  ; ite∙ = λ t a a' → iteNf (π₂ t) (π₂ a) (π₂ a')
  ; iteβ₁∙ = refl
  ; iteβ₂∙ = refl
  ; true[]∙ = λ where {γ = σ} → true[]Nf {σ = π₂ σ}
  ; false[]∙ = λ where {γ = σ} → false[]Nf {σ = π₂ σ}
  ; ite[]∙ = λ where {γ = σ} → ite[]Nf {σ = π₂ σ}
  ; num∙ = numNf
  ; isZero∙ = λ t → isZeroNf (π₂ t)
  ; _+o∙_ = λ t t' → π₂ t +NfNf π₂ t'
  ; isZeroβ₁∙ = refl
  ; isZeroβ₂∙ = refl
  ; +β∙ = refl
  ; num[]∙ = λ where {γ = σ} → num[]Nf {σ = π₂ σ}
  ; isZero[]∙ = λ where {γ = σ} → isZero[]Nf {σ = π₂ σ}
  ; +[]∙ = λ where {γ = σ} → +[]Nf {σ = π₂ σ}
  }
module N = ParaModel N

norm : ∀{Γ A} → Tm Γ A → Nf Γ A
norm = N.⟦_⟧t

ex1 : norm (ite (isZero (num 1 +o num 2)) (v 0) false) ≡ falseNf {◇ ▹ Bool}
ex1 = refl

ex2 : norm (def (num 1) ((v 0 +o v 0) +o ite false (v 0) (v 0))) ≡ numNf {◇} 3
ex2 = refl

not-equal' : ¬ (
  I.ite (I.isZero (I.num 2)) (I.num 3) (I.num 12) ≡
  I.ite (I.isZero (I.num 0 I.+o I.num 0)) (I.num 11) (I.num {I.◇} 3))
not-equal' e = 12≠11 (cong norm e)
  where
    12≠11 : ¬ (numNf 12 ≡ numNf 11)
    12≠11 ()

ex-open' : ¬ (isZero (v 0 {◇ ▹ Nat} +o num 2) ≡ false)
ex-open' e with cong norm e
... | ()

⌜⁺⌝         :  ∀{Γ Δ A}{σ : SubNf Δ Γ} → ⌜ _⁺Nf {A = A} σ ⌝SubNf ≡ ⌜ σ ⌝SubNf ⁺
⌜isZeroNf⌝  :  ∀{Γ}{t : Nf Γ Nat} → ⌜ isZeroNf t ⌝Nf ≡ isZero ⌜ t ⌝Nf
⌜iteNf⌝     :  ∀{Γ A}{t : Nf Γ Bool}{u v : Nf Γ A} →
               ⌜ iteNf t u v ⌝Nf ≡ ite ⌜ t ⌝Nf ⌜ u ⌝Nf ⌜ v ⌝Nf
⌜+NfNf⌝     :  ∀{Γ}{t t' : Nf Γ Nat} → ⌜ t +NfNf t' ⌝Nf ≡ ⌜ t ⌝Nf +o ⌜ t' ⌝Nf
⌜[]VWk⌝     :  ∀{Γ A}{x : Var Γ A}{Δ}{σ : Wk Δ Γ} →
               var (x [ σ ]VWk) ≡ var x [ ⌜ σ ⌝Wk ]
⌜[]NeWk⌝    :  ∀{Γ A}{t : Ne Γ A}{Δ}{σ : Wk Δ Γ} →
               ⌜ t [ σ ]NeWk ⌝Ne ≡ ⌜ t ⌝Ne [ ⌜ σ ⌝Wk ]
⌜[]NfWk⌝    :  ∀{Γ A}{t : Nf Γ A}{Δ}{σ : Wk Δ Γ} →
               ⌜ t [ σ ]NfWk ⌝Nf ≡ ⌜ t ⌝Nf [ ⌜ σ ⌝Wk ]
⌜[]VSub1⌝   :  ∀{Γ A}{x : Var Γ A}{Δ}{σ : Sub1 Δ Γ} →
               ⌜ x [ σ ]VSub1 ⌝Nf ≡ var x [ ⌜ σ ⌝Sub1 ]
⌜[]NeSub1⌝  :  ∀{Γ A}{t : Ne Γ A}{Δ}{σ : Sub1 Δ Γ} →
               ⌜ t [ σ ]NeSub1 ⌝Nf ≡ ⌜ t ⌝Ne [ ⌜ σ ⌝Sub1 ]
⌜[]NfSub1⌝  :  ∀{Γ A}{t : Nf Γ A}{Δ}{σ : Sub1 Δ Γ} →
               ⌜ t [ σ ]NfSub1 ⌝Nf ≡ ⌜ t ⌝Nf [ ⌜ σ ⌝Sub1 ]
⌜[]V⌝       :  ∀{Γ A}{x : Var Γ A}{Δ}{σ : SubNf Δ Γ} →
               ⌜ x [ σ ]V ⌝Nf ≡ var x [ ⌜ σ ⌝SubNf ]
⌜[]Ne⌝      :  ∀{Γ A}{t : Ne Γ A}{Δ}{σ : SubNf Δ Γ} →
               ⌜ t [ σ ]Ne ⌝Nf ≡ ⌜ t ⌝Ne [ ⌜ σ ⌝SubNf ]
⌜[]Nf⌝      :  ∀{Γ A}{t : Nf Γ A}{Δ}{σ : SubNf Δ Γ} →
               ⌜ t [ σ ]Nf ⌝Nf ≡ ⌜ t ⌝Nf [ ⌜ σ ⌝SubNf ]

⌜⁺⌝ {σ = ι₁ σ} = refl
⌜⁺⌝ {σ = ι₂ σ} = refl

⌜isZeroNf⌝ {t = neu _} = refl
⌜isZeroNf⌝ {t = numNf zero} = isZeroβ₁ ⁻¹
⌜isZeroNf⌝ {t = numNf (suc n)} = isZeroβ₂ ⁻¹

⌜iteNf⌝ {t = neu _} = refl
⌜iteNf⌝ {t = trueNf} = iteβ₁ ⁻¹
⌜iteNf⌝ {t = falseNf} = iteβ₂ ⁻¹

⌜+NfNf⌝ {t = neu t} {t' = neu t'} = refl
⌜+NfNf⌝ {t = neu t} {t' = numNf n'} = refl
⌜+NfNf⌝ {t = numNf n} {t' = neu t'} = refl
⌜+NfNf⌝ {t = numNf n} {t' = numNf n'} = +β ⁻¹

⌜[]VWk⌝ {x = x} {σ = p} = [p] ⁻¹
⌜[]VWk⌝ {x = vz} {σ = σ ⁺Wk} = vz[⁺] ⁻¹
⌜[]VWk⌝ {x = vs x} {σ = σ ⁺Wk} = [p] ⁻¹ ◾ cong _[ p ] (⌜[]VWk⌝ {x = x}{σ = σ}) ◾ vs[⁺] ⁻¹

⌜[]NeWk⌝ {t = varNe x}     {σ = σ} = ⌜[]VWk⌝ {x = x}
⌜[]NeWk⌝ {t = iteNe t u v} {σ = σ} = cong (λ z → ite (π₁ z) (π₁ (π₂ z)) (π₂ (π₂ z))) (⌜[]NeWk⌝ {t = t}{σ = σ} ,= ⌜[]NfWk⌝ {t = u}{σ = σ} ,= ⌜[]NfWk⌝ {t = v}{σ = σ}) ◾ ite[] ⁻¹
⌜[]NeWk⌝ {t = isZeroNe t}  {σ = σ} = cong isZero (⌜[]NeWk⌝ {t = t}{σ = σ}) ◾ isZero[] ⁻¹
⌜[]NeWk⌝ {t = t +NeNe t'}  {σ = σ} = cong (λ z → π₁ z +o π₂ z) (⌜[]NeWk⌝ {t = t}{σ = σ} ,= ⌜[]NeWk⌝ {t = t'}{σ = σ}) ◾ +[] ⁻¹
⌜[]NeWk⌝ {t = t +NeNf n'}  {σ = σ} = cong (λ z → π₁ z +o π₂ z) (⌜[]NeWk⌝ {t = t}{σ = σ} ,= num[] ⁻¹) ◾ +[] ⁻¹
⌜[]NeWk⌝ {t = n +NfNe t'}  {σ = σ} = cong (λ z → π₁ z +o π₂ z) (num[] ⁻¹ ,= ⌜[]NeWk⌝ {t = t'}{σ = σ}) ◾ +[] ⁻¹
⌜[]NfWk⌝ {t = neu t}       {σ = σ} = ⌜[]NeWk⌝ {t = t}
⌜[]NfWk⌝ {t = trueNf}      {σ = σ} = true[] ⁻¹
⌜[]NfWk⌝ {t = falseNf}     {σ = σ} = false[] ⁻¹
⌜[]NfWk⌝ {t = numNf _}     {σ = σ} = num[] ⁻¹

⌜[]VSub1⌝ {x = vz}   {σ = ⟨ t ⟩Sub1} = vz[⟨⟩] ⁻¹
⌜[]VSub1⌝ {x = vs x} {σ = ⟨ t ⟩Sub1} = vs[⟨⟩] ⁻¹
⌜[]VSub1⌝ {x = vz}   {σ = σ ⁺Sub1} = vz[⁺] ⁻¹
⌜[]VSub1⌝ {x = vs x} {σ = σ ⁺Sub1} = ⌜[]NfWk⌝ {t = x [ σ ]VSub1}{σ = p} ◾ cong _[ p ] (⌜[]VSub1⌝ {x = x}{σ = σ}) ◾ vs[⁺] ⁻¹

⌜[]NeSub1⌝ {t = varNe x}     {σ = σ} = ⌜[]VSub1⌝ {x = x}
⌜[]NeSub1⌝ {t = iteNe t u v} {σ = σ} = ⌜iteNf⌝ {t = t [ σ ]NeSub1} ◾ cong (λ z → ite (π₁ z) (π₁ (π₂ z)) (π₂ (π₂ z))) (⌜[]NeSub1⌝ {t = t}{σ = σ} ,= ⌜[]NfSub1⌝ {t = u}{σ = σ} ,= ⌜[]NfSub1⌝ {t = v}{σ = σ}) ◾ ite[] ⁻¹
⌜[]NeSub1⌝ {t = isZeroNe t}  {σ = σ} = ⌜isZeroNf⌝ {t = t [ σ ]NeSub1} ◾ cong isZero (⌜[]NeSub1⌝ {t = t}{σ = σ}) ◾ isZero[] ⁻¹
⌜[]NeSub1⌝ {t = t +NeNe t'}  {σ = σ} = ⌜+NfNf⌝ {t = t [ σ ]NeSub1}{t' = t' [ σ ]NeSub1} ◾ cong (λ z → π₁ z +o π₂ z) (⌜[]NeSub1⌝ {t = t}{σ = σ} ,= ⌜[]NeSub1⌝ {t = t'}{σ = σ}) ◾ +[] ⁻¹
⌜[]NeSub1⌝ {t = t +NeNf n'}  {σ = σ} = ⌜+NfNf⌝ {t = t [ σ ]NeSub1} ◾ cong (λ z → π₁ z +o π₂ z) (⌜[]NeSub1⌝ {t = t}{σ = σ} ,= num[] ⁻¹) ◾ +[] ⁻¹
⌜[]NeSub1⌝ {t = n +NfNe t'}  {σ = σ} = ⌜+NfNf⌝ {t = numNf n}{t' = t' [ σ ]NeSub1} ◾ cong (λ z → π₁ z +o π₂ z) (num[] ⁻¹ ,= ⌜[]NeSub1⌝ {t = t'}{σ = σ}) ◾ +[] ⁻¹
⌜[]NfSub1⌝ {t = neu t}       {σ = σ} = ⌜[]NeSub1⌝ {t = t}{σ = σ}
⌜[]NfSub1⌝ {t = trueNf}      {σ = σ} = true[] ⁻¹
⌜[]NfSub1⌝ {t = falseNf}     {σ = σ} = false[] ⁻¹
⌜[]NfSub1⌝ {t = numNf n}     {σ = σ} = num[] ⁻¹

⌜[]V⌝ {x = x} {σ = ι₁ σ} = ⌜[]VWk⌝ {x = x}{σ = σ}
⌜[]V⌝ {x = x} {σ = ι₂ σ} = ⌜[]VSub1⌝ {x = x}{σ = σ}

⌜[]Ne⌝ {t = t} {σ = ι₁ σ} = ⌜[]NeWk⌝ {t = t}{σ = σ}
⌜[]Ne⌝ {t = t} {σ = ι₂ σ} = ⌜[]NeSub1⌝ {t = t}{σ = σ}

⌜[]Nf⌝ {t = t} {σ = ι₁ σ} = ⌜[]NfWk⌝ {t = t}{σ = σ}
⌜[]Nf⌝ {t = t} {σ = ι₂ σ} = ⌜[]NfSub1⌝ {t = t}{σ = σ}

open import Def.DepModel
Comp : DepModel
Comp = record
  { Ty∙ = λ _ → Lift ⊤
  ; Nat∙ = _
  ; Bool∙ = _
  ; Con∙ = λ _ → Lift ⊤
  ; ◇∙ = _
  ; _▹∙_ = _
  ; Var∙ = λ _ _ _ → Lift ⊤
  ; vz∙ = _
  ; vs∙ = _
  ; Tm∙ = λ {Γ}{A} _ _ t → Lift (⌜ N.⟦ t ⟧t ⌝Nf ≡ t)
  ; Sub∙ = λ _ _ σ → Lift (⌜ N.⟦ σ ⟧s ⌝SubNf ≡ σ)
  ; p∙ = mk refl
  ; ⟨_⟩∙ = λ e → mk (cong ⟨_⟩ (un e))
  ; _⁺∙ = λ where {A = A}{σ = σ} e → mk (⌜⁺⌝ {A = A}{N.⟦ σ ⟧s} ◾ cong _⁺ (un e))
  ; var∙ = λ _ → mk refl
  ; _[_]∙ =
    λ where {t = t}{σ = σ} te σe →
             mk  (⌜[]Nf⌝ {t = N.⟦ t ⟧t}{σ = N.⟦ σ ⟧s} ◾
                 cong (λ z → π₁ z [ π₂ z ]) (un te ,= un σe))
  ; [p]∙ = refl
  ; vz[⟨⟩]∙ = refl
  ; vz[⁺]∙ = refl
  ; vs[⟨⟩]∙ = refl
  ; vs[⁺]∙ = refl
  ; true∙ = mk refl
  ; false∙ = mk refl
  ; ite∙ =
    λ where {t = t}{u = u}{v = v} te ue ve →
             mk  (⌜iteNf⌝ {t = N.⟦ t ⟧t}{u = N.⟦ u ⟧t}{v = N.⟦ v ⟧t} ◾
                 cong (λ z → ite (π₁ z) (π₁ (π₂ z)) (π₂ (π₂ z))) (un te ,= un ue ,= un ve))
  ; iteβ₁∙ = refl
  ; iteβ₂∙ = refl
  ; true[]∙ = refl
  ; false[]∙ = refl
  ; ite[]∙ = refl
  ; num∙ = λ _ → mk refl
  ; isZero∙ = λ where {t = t} te → mk (⌜isZeroNf⌝ {t = N.⟦ t ⟧t} ◾ cong isZero (un te))
  ; _+o∙_ =
    λ where {u = u}{v} ue ve →
             mk  (⌜+NfNf⌝ {t = N.⟦ u ⟧t}{N.⟦ v ⟧t} ◾
                 cong (λ z → π₁ z +o π₂ z) (un ue ,= un ve))
  ; isZeroβ₁∙ = refl
  ; isZeroβ₂∙ = refl
  ; +β∙ = refl
  ; num[]∙ = refl
  ; isZero[]∙ = refl
  ; +[]∙ = refl
  }
module Comp = DepModel Comp

compl : ∀{Γ A}(t : Tm Γ A) → ⌜ norm t ⌝Nf ≡ t
compl t = un Comp.⟦ t ⟧t

e4 : ite true (num 3 +o num 2) (num 0) ≡ num 1 +o (num 2 +o (num 1 +o num {◇} 1))
e4 =
  ite true (num 3 +o num 2) (num 0)
                                     ≡⟨ compl (ite true (num 3 +o num 2) (num 0)) ⁻¹ ⟩
  num 5
                                     ≡⟨ compl (num 1 +o (num 2 +o (num 1 +o num 1))) ⟩
  num 1 +o (num 2 +o (num 1 +o num 1))
                                     ∎

stabNe : ∀{Γ A}(t : Ne Γ A) → norm ⌜ t ⌝Ne ≡ neu t
stabNf : ∀{Γ A}(t : Nf Γ A) → norm ⌜ t ⌝Nf ≡ t

stabNe (varNe x) = refl
stabNe (iteNe t a a') = cong₃ iteNf (stabNe t) (stabNf a) (stabNf a')
stabNe (isZeroNe t) = cong isZeroNf (stabNe t)
stabNe (t +NeNe t') = cong₂ _+NfNf_ (stabNe t) (stabNe t')
stabNe (t +NeNf n') = cong (_+NfNf numNf n') (stabNe t)
stabNe (n +NfNe t') = cong (numNf n +NfNf_) (stabNe t')
stabNf (neu t) = stabNe t
stabNf trueNf = refl
stabNf falseNf = refl
stabNf (numNf n) = refl

infix 4 _≟ℕ_ _≟Ty_ _≟Var_ _≟Ne_ _≟Nf_ _≟Tm_ 

_≟ℕ_ : (m n : ℕ) → Dec (Lift (m ≡ n))
zero  ≟ℕ zero    = ι₁ (mk refl)
zero  ≟ℕ suc n   = ι₂ (mk λ { (mk ()) })
suc m ≟ℕ zero    = ι₂ (mk λ { (mk ()) })
suc m ≟ℕ suc n   with m ≟ℕ n
... | ι₁ (mk e)  = ι₁ (mk (cong suc e))
... | ι₂ f       = ι₂ (mk λ { (mk refl) → un f (mk refl)})

_≟Ty_ : (A B : Ty) → Dec (Lift (A ≡ B))

Bool  ≟Ty Bool  = ι₁ (mk refl)
Bool  ≟Ty Nat   = ι₂ (mk λ { (mk ()) })
Nat   ≟Ty Nat   = ι₁ (mk refl)
Nat   ≟Ty Bool  = ι₂ (mk λ { (mk ()) })

_≟Var_ : ∀{Γ A₀ A₁}(x₀ : Var Γ A₀)(x₁ : Var Γ A₁) →
  Dec (Σ (Lift (A₀ ≡ A₁)) λ e → Lift (transp (Var Γ) (un e) x₀ ≡ x₁))

vz      ≟Var vz         = ι₁ (mk refl , mk refl)
vz      ≟Var (vs x₁)    = ι₂ (mk λ { (mk refl , ()) })
(vs x₀) ≟Var vz         = ι₂ (mk λ { (mk refl , ()) })
(vs x₀) ≟Var (vs x₁)    with x₀ ≟Var x₁
... | ι₁ (mk E , mk e)  = ι₁ (mk E , mk (transp$i vs E {x₀} ⁻¹ ◾ cong vs e))
... | ι₂ f              = ι₂ (mk (λ { (mk refl , mk refl) → un f (mk refl , mk refl) }))

congditeNe : ∀{Γ A₀ A₁}(A₀₁ : A₀ ≡ A₁){t₀ t₁}(t₀₁ : t₀ ≡ t₁){a₀ a₁} → transp (Nf Γ) A₀₁ a₀ ≡ a₁ →
  ∀{a'₀ a'₁} → transp (Nf Γ) A₀₁ a'₀ ≡ a'₁ →
  transp (Ne Γ) A₀₁ (iteNe t₀ a₀ a'₀) ≡ iteNe t₀ (transp (Nf Γ) A₀₁ a₀) (transp (Nf Γ) A₀₁ a'₀)
congditeNe refl refl refl refl = refl

_≟Ne_ : ∀{Γ A₀ A₁}(a₀ : Ne Γ A₀)(a₁ : Ne Γ A₁) →
  Dec (Σ (Lift (A₀ ≡ A₁)) λ e → Lift (transp (Ne Γ) (un e) a₀ ≡ a₁))
_≟Nf_ : ∀{Γ A}(a₀ a₁ : Nf Γ A) → Dec (Lift (a₀ ≡ a₁))

varNe x₀              ≟Ne varNe x₁              with x₀ ≟Var x₁
... | ι₁ (mk E , mk e)                          = ι₁ (mk E , mk (transp$i varNe E {x₀} ⁻¹ ◾ cong varNe e))
... | ι₂ f                                      = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl , mk refl) })
varNe _               ≟Ne iteNe _ _ _           = ι₂ (mk λ { (mk refl , mk ()) })
varNe _               ≟Ne isZeroNe _            = ι₂ (mk λ { (mk refl , mk ()) })
varNe _               ≟Ne (_ +NeNe _)           = ι₂ (mk λ { (mk refl , mk ()) })
varNe _               ≟Ne (_ +NeNf _)           = ι₂ (mk λ { (mk refl , mk ()) })
varNe _               ≟Ne (_ +NfNe _)           = ι₂ (mk λ { (mk refl , mk ()) })
iteNe _ _ _           ≟Ne varNe _               = ι₂ (mk λ { (mk refl , mk ()) })
iteNe {A₀} t₀ a₀ a'₀  ≟Ne iteNe {A₁} t₁ a₁ a'₁  with A₀ ≟Ty A₁ | t₀ ≟Ne t₁
... | ι₁ _ | ι₂ f                               = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl , mk refl) })
... | ι₂ f | _                                  = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl) })
... | ι₁ (mk A₀₁) | ι₁ (mk _ , mk t₀₁)          with transp (Nf _) A₀₁ a₀ ≟Nf a₁ | transp (Nf _) A₀₁ a'₀ ≟Nf a'₁
... | ι₁ (mk a₀₁) | ι₁ (mk a'₀₁)                = ι₁ (mk A₀₁ , mk (congditeNe A₀₁ t₀₁ a₀₁ a'₀₁ ◾
                                                                   cong₃ iteNe t₀₁ a₀₁ a'₀₁))
... | ι₁ _ | ι₂ f                               = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl) })
... | ι₂ f | _                                  = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl) })
iteNe _ _ _           ≟Ne isZeroNe _            = ι₂ (mk λ { (mk refl , mk ()) })
iteNe _ _ _           ≟Ne (_ +NeNe _)           = ι₂ (mk λ { (mk refl , mk ()) })
iteNe _ _ _           ≟Ne (_ +NeNf _)           = ι₂ (mk λ { (mk refl , mk ()) })
iteNe _ _ _           ≟Ne (_ +NfNe _)           = ι₂ (mk λ { (mk refl , mk ()) })
isZeroNe _            ≟Ne varNe _               = ι₂ (mk λ { (mk refl , mk ()) })
isZeroNe _            ≟Ne iteNe _ _ _           = ι₂ (mk λ { (mk refl , mk ()) })
isZeroNe t₀           ≟Ne isZeroNe t₁           with t₀ ≟Ne t₁
... | ι₁ (mk _ , mk e)                          = ι₁ (mk refl , mk (cong isZeroNe e))
... | ι₂ f                                      = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl , mk refl) })
isZeroNe _            ≟Ne (_ +NeNe _)           = ι₂ (mk λ { (mk () , _) })
isZeroNe _            ≟Ne (_ +NeNf _)           = ι₂ (mk λ { (mk () , _) })
isZeroNe _            ≟Ne (_ +NfNe _)           = ι₂ (mk λ { (mk () , _) })
(_ +NeNe _)           ≟Ne varNe _               = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NeNe _)           ≟Ne iteNe _ _ _           = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NeNe _)           ≟Ne isZeroNe _            = ι₂ (mk λ { (mk () , _) })
(t₀ +NeNe t'₀)        ≟Ne (t₁ +NeNe t'₁)        with t₀ ≟Ne t₁ | t'₀ ≟Ne t'₁
... | ι₁ (mk E , mk e) | ι₁ (mk E' , mk e')     = ι₁ (mk refl , mk (cong₂ _+NeNe_ e e'))
... | ι₁ _ | ι₂ f                               = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl , mk refl) })
... | ι₂ f | _                                  = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl , mk refl) })
(_ +NeNe _)           ≟Ne (_ +NeNf _)           = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NeNe _)           ≟Ne (_ +NfNe _)           = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NeNf _)           ≟Ne varNe _               = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NeNf _)           ≟Ne iteNe _ _ _           = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NeNf _)           ≟Ne isZeroNe _            = ι₂ (mk λ { (mk () , _) })
(_ +NeNf _)           ≟Ne (_ +NeNe _)           = ι₂ (mk λ { (mk refl , mk ()) })
(t₀ +NeNf n'₀)        ≟Ne (t₁ +NeNf n'₁)        with t₀ ≟Ne t₁ | n'₀ ≟ℕ n'₁
... | ι₁ (mk _ , mk e) | ι₁ (mk e')             = ι₁ (mk refl , mk (cong₂ _+NeNf_ e e'))
... | ι₁ _ | ι₂ f                               = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl) })
... | ι₂ f | _                                  = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl , mk refl) })
(_ +NeNf _)           ≟Ne (_ +NfNe _)           = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NfNe _)           ≟Ne varNe _               = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NfNe _)           ≟Ne iteNe _ _ _           = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NfNe _)           ≟Ne isZeroNe _            = ι₂ (mk λ { (mk () , _) })
(_ +NfNe _)           ≟Ne (_ +NeNe _)           = ι₂ (mk λ { (mk refl , mk ()) })
(_ +NfNe _)           ≟Ne (_ +NeNf _)           = ι₂ (mk λ { (mk refl , mk ()) })
(n₀ +NfNe t'₀)        ≟Ne (n₁ +NfNe t'₁)        with n₀ ≟ℕ n₁ | t'₀ ≟Ne t'₁
... | ι₁ (mk e) | ι₁ (mk _ , mk e')             = ι₁ (mk refl , mk (cong₂ _+NfNe_ e e'))
... | ι₁ _ | ι₂ f                               = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl , mk refl) })
... | ι₂ f | _                                  = ι₂ (mk λ { (mk refl , mk refl) → un f (mk refl) })
neu a₀   ≟Nf (neu a₁)   with a₀ ≟Ne a₁
... | ι₁ (mk _ , mk e)  = ι₁ (mk (cong neu e))
... | ι₂ f              = ι₂ (mk λ { (mk refl) → un f (mk refl , mk refl) })
neu _    ≟Nf trueNf     = ι₂ (mk λ { (mk ()) })
neu _    ≟Nf falseNf    = ι₂ (mk λ { (mk ()) })
neu _    ≟Nf numNf _    = ι₂ (mk λ { (mk ()) })
trueNf   ≟Nf neu _      = ι₂ (mk λ { (mk ()) })
trueNf   ≟Nf trueNf     = ι₁ (mk refl)
trueNf   ≟Nf falseNf    = ι₂ (mk λ { (mk ()) })
falseNf  ≟Nf neu _      = ι₂ (mk λ { (mk ()) })
falseNf  ≟Nf trueNf     = ι₂ (mk λ { (mk ()) })
falseNf  ≟Nf falseNf    = ι₁ (mk refl)
numNf _  ≟Nf neu _      = ι₂ (mk λ { (mk ()) })
numNf n₀ ≟Nf numNf n₁   with n₀ ≟ℕ n₁
... | ι₁ (mk e)         = ι₁ (mk (cong numNf e))
... | ι₂ f              = ι₂ (mk λ { (mk refl) → un f (mk refl) })

_≟Tm_ : ∀{Γ A}(t₀ t₁ : Tm Γ A) → Dec (Lift (t₀ ≡ t₁))
t₀ ≟Tm t₁ with norm t₀ ≟Nf norm t₁
... | ι₁ (mk e) = ι₁ (mk (compl t₀ ⁻¹ ◾ cong ⌜_⌝Nf e ◾ compl t₁))
... | ι₂ f = ι₂ (mk λ t₀₁ → un f (mk (cong norm (un t₀₁))))

ex3 : isZero (v 0 +o num 2) [ ⟨ num {◇} 0 ⟩ ] ≡ false
ex3 = extract (isZero (v 0 +o num 2) [ ⟨ num {◇} 0 ⟩ ] ≟Tm false)

ex-open'' : ¬ (isZero (var (vz {◇}) +o num 2) ≡ false)
ex-open'' = extract' (isZero (var vz +o num 2) ≟Tm false)

true≠false : ∀{Γ} → ¬ (I.true {Γ} ≡ I.false)
true≠false e = trueNf≠falseNf (cong norm e)
  where
    trueNf≠falseNf : ∀{Γ} → ¬ (trueNf {Γ} ≡ falseNf)
    trueNf≠falseNf ()

num-inj : ∀{Γ m n} → I.num {Γ} m ≡ I.num n → m ≡ n
num-inj e = numNf-inj (cong norm e)
  where
    numNf-inj : ∀{Γ m n} → numNf {Γ} m ≡ numNf n → m ≡ n
    numNf-inj refl = refl

isZero=true : ∀{Γ} → I.isZero {Γ} (I.num 0) ≡ I.true
isZero=true = I.isZeroβ₁

isZero-not-inj : ¬ (∀{Γ t t'} → isZero {Γ} t ≡ isZero t' → t ≡ t')
isZero-not-inj H = 1≠2 (num-inj (H {I.◇}{I.num 1}{I.num 2} (I.isZeroβ₂ ◾ I.isZeroβ₂ ⁻¹)))
  where
    1≠2 : ¬ (1 ≡ 2)
    1≠2 ()

infixl 5 _$_

Fun : Con → Ty → Ty → Set
Fun Γ A B = Tm (Γ ▹ A) B

lam : ∀{Γ A B} → Tm (Γ ▹ A) B → Fun Γ A B
lam t = t

_$_ : ∀{Γ A B} → Fun Γ A B → Tm Γ A → Tm Γ B
t $ u = t [ ⟨ u ⟩ ]
