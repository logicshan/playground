\subsection{Another example of normalisation: integers}

In this subsection, we define integers as the initial model of an algebraic theory. We illustrate the concepts of model, syntax, iterator, dependent model, induction, normalisation, completeness and stability of normalisation. The representation of integers is from \cite{10.1145/3373718.3394760}.

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}

module Int where

open import Lib

module I where
  postulate
    Z     : Set
    Zero  : Z
    Suc   : Z → Z
    Pred  : Z → Z
    SucPred : (i : Z) → Suc (Pred i) ≡ i
    PredSuc : (i : Z) → Pred (Suc i) ≡ i
\end{code}

An integer model has five components, a set, a zero element, a successor operation, a predecessor operation and two equalities saying that successor after or before predecessor is the identity.
\begin{code}
record Model {ℓ} : Set (lsuc ℓ) where
  field
    Z        : Set ℓ
    Zero     : Z
    Suc      : Z → Z
    Pred     : Z → Z
    SucPred  : (i : Z) → Suc (Pred i) ≡ i
    PredSuc  : (i : Z) → Pred (Suc i) ≡ i
\end{code}
We have an iterator, that is a homomorphism from the initial model to any model.
\begin{code}
  postulate
    ⟦_⟧      : I.Z → Z
    ⟦Zero⟧   :         ⟦ I.Zero    ⟧ ≈ Zero
    ⟦Suc⟧    : ∀{i} →  ⟦ I.Suc i   ⟧ ≈ Suc ⟦ i ⟧
    ⟦Pred⟧   : ∀{i} →  ⟦ I.Pred i  ⟧ ≈ Pred ⟦ i ⟧
\end{code}
\begin{code}[hide]
    {-# REWRITE ⟦Zero⟧ ⟦Suc⟧ ⟦Pred⟧ #-}
\end{code}
Integers themselves are given by the initial integer model.
\begin{code}
ℤ = I.Z
\end{code}
There are multiple representations of each number, e.g.\ $-1$ is given by
\verb$Pred Zero$, \verb$Pred (Suc (Pred Zero))$, and so on.

Examples of equalities which hold in any integer model.
\begin{code}
module examples {ℓ}(M : Model {ℓ}) where
  open Model M
  
  eq1 : Pred (Suc (Pred Zero)) ≡ Pred Zero
  eq1 = PredSuc (Pred Zero)

  eq2 : Pred (Suc (Suc (Pred Zero)))  ≡ Zero
  eq2 = Pred (Suc (Suc (Pred Zero)))
                                      ≡⟨ PredSuc (Suc (Pred Zero)) ⟩
        Suc (Pred Zero)
                                      ≡⟨ SucPred Zero ⟩ 
        Zero                          ∎
\end{code}

Dependent models and induction.
\begin{code}[hide]
record DepModel {ℓ} : Set (lsuc ℓ) where
  field
    Z∙       : I.Z → Set ℓ
    Zero∙    : Z∙ I.Zero
    Suc∙     : ∀{i} → Z∙ i → Z∙ (I.Suc  i)
    Pred∙    : ∀{i} → Z∙ i → Z∙ (I.Pred i)
    SucPred∙ : ∀{i}(i∙ : Z∙ i) → (Z∙ ~) (I.SucPred i) (Suc∙ (Pred∙ i∙)) i∙
    PredSuc∙ : ∀{i}(i∙ : Z∙ i) → (Z∙ ~) (I.PredSuc i) (Pred∙ (Suc∙ i∙)) i∙
  postulate
    ⟦_⟧      : (i : I.Z) → Z∙ i
    ⟦Zero⟧   :         ⟦ I.Zero     ⟧ ≈ Zero∙
    ⟦Suc⟧    : ∀{i} →  ⟦ I.Suc i    ⟧ ≈ Suc∙   ⟦ i ⟧
    ⟦Pred⟧   : ∀{i} →  ⟦ I.Pred i   ⟧ ≈ Pred∙  ⟦ i ⟧
    {-# REWRITE ⟦Zero⟧ #-}
\end{code}

The model \verb$M i$ where \verb$Zero$ is \verb$i$, everything else comes from the syntax.
\begin{code}
M : I.Z → Model
M i = record
  { Z        = I.Z
  ; Zero     = i
  ; Suc      = I.Suc
  ; Pred     = I.Pred
  ; SucPred  = I.SucPred
  ; PredSuc  = I.PredSuc
  }
module M i = Model (M i)
\end{code}
Now we have addition \verb$j +ℤ i$ which replaces \verb$I.Zero$ inside \verb$j$ by \verb$i$:
\begin{code}
_+ℤ_ : I.Z → I.Z → I.Z
j +ℤ i = M.⟦_⟧ i j

test+ : {i : I.Z} → I.Suc (I.Suc (I.Pred I.Zero)) +ℤ i ≡ I.Suc (I.Suc (I.Pred i))
test+ {i} = refl

test+' : {i : I.Z} → I.Pred (I.Suc (I.Suc (I.Pred I.Zero))) +ℤ i ≡ I.Pred (I.Suc (I.Suc (I.Pred i)))
test+' {i} = refl
\end{code}

Integers were defined using a language with equations. Normal forms of
integers are defined by another language without
equations. Normalisation means that the syntaxes of these two
languages are in bijection: there is a bijection between \verb$I.Z$
and \verb$Nf$ (we don't use other models of the language of normal
forms, we only work with its syntax \verb$Nf$).

Normal forms and examples.
\begin{code}
data Nf  : Set where
  -Suc   : ℕ → Nf
  Zero   : Nf
  +Suc   : ℕ → Nf

minusThree minusFive plusSix : Nf
minusThree  = -Suc 2
minusFive   = -Suc 4
plusSix     = +Suc 5

SucNf : Nf → Nf
SucNf (-Suc zero)      = Zero
SucNf (-Suc (suc n))   = -Suc n
SucNf Zero             = +Suc 0
SucNf (+Suc n)         = +Suc (suc n)

PredNf : Nf → Nf
PredNf (-Suc n)        = -Suc (suc n)
PredNf Zero            = -Suc 0
PredNf (+Suc zero)     = Zero
PredNf (+Suc (suc n))  = +Suc n
\end{code}

Normalisation.
\begin{code}
N : Model
N = record
  { Z       = Nf
  ; Zero    = Zero
  ; Suc     = SucNf
  ; Pred    = PredNf
  ; SucPred = λ  { (-Suc zero)     → refl
                 ; (-Suc (suc n))  → refl
                 ; Zero            → refl
                 ; (+Suc zero)     → refl
                 ; (+Suc (suc n))  → refl
                 }
  ; PredSuc = λ  { (-Suc zero)     → refl
                 ; (-Suc (suc n))  → refl
                 ; Zero            → refl
                 ; (+Suc zero)     → refl
                 ; (+Suc (suc n))  → refl }
  }
module N = Model N

norm : I.Z → Nf
norm = N.⟦_⟧
\end{code}
Quoting normal forms into integers:
\begin{code}
⌜_⌝ : Nf → I.Z
⌜ -Suc zero     ⌝ = I.Pred I.Zero
⌜ -Suc (suc n)  ⌝ = I.Pred ⌜ -Suc n ⌝
⌜ Zero          ⌝ = I.Zero
⌜ +Suc zero     ⌝ = I.Suc I.Zero
⌜ +Suc (suc n)  ⌝ = I.Suc ⌜ +Suc n ⌝
\end{code}
A unit test for normalisation:
\begin{code}
testnorm :  ⌜ norm (I.Pred (I.Pred (I.Suc (I.Pred (I.Pred (I.Pred (I.Suc I.Zero))))))) ⌝ ≡
            I.Pred (I.Pred (I.Pred I.Zero))
testnorm = refl
\end{code}
Stability of normalisation:
\begin{code}
stab : (v : Nf) → norm ⌜ v ⌝ ≡ v
stab (-Suc zero)     = refl
stab (-Suc (suc n))  = cong PredNf (stab (-Suc n))
stab Zero            = refl
stab (+Suc zero)     = refl
stab (+Suc (suc n))  = cong SucNf (stab (+Suc n))
\end{code}
Helper lemmas for completeness:
\begin{code}
⌜Suc⌝ : (v : Nf) → ⌜ SucNf v ⌝ ≡ I.Suc ⌜ v ⌝
⌜Suc⌝ (-Suc zero)      = I.SucPred I.Zero ⁻¹
⌜Suc⌝ (-Suc (suc n))   = I.SucPred ⌜ -Suc n ⌝ ⁻¹
⌜Suc⌝ Zero             = refl 
⌜Suc⌝ (+Suc n)         = refl

⌜Pred⌝ : (v : Nf) → ⌜ PredNf v ⌝ ≡ I.Pred ⌜ v ⌝
⌜Pred⌝ (-Suc n)        = refl
⌜Pred⌝ Zero            = refl
⌜Pred⌝ (+Suc zero)     = I.PredSuc I.Zero ⁻¹
⌜Pred⌝ (+Suc (suc n))  = I.PredSuc ⌜ +Suc n ⌝ ⁻¹
\end{code}
Completeness of normalisation:
\begin{code}
Comp : DepModel
Comp = record
  { Z∙       = λ i → Lift (⌜ norm i ⌝ ≡ i)
  ; Zero∙    = mk refl
  ; Suc∙     = λ {i} i∙ → mk (⌜Suc⌝ N.⟦ i ⟧ ◾ cong I.Suc (un i∙))
  ; Pred∙    = λ {i} i∙ → mk (⌜Pred⌝ N.⟦ i ⟧ ◾ cong I.Pred (un i∙))
  ; SucPred∙ = λ _ → refl
  ; PredSuc∙ = λ _ → refl
  }
module Comp = DepModel Comp

comp : (i : I.Z) → ⌜ norm i ⌝ ≡ i
comp i = un (Comp.⟦ i ⟧)
\end{code}

\begin{exe}
Prove that integers form a commutative monoid with addition.
\end{exe}

\begin{exe}
Define multiplication and prove that integers form a commutative ring with addition and multiplication.
\end{exe}
