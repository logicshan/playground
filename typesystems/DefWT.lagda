\subsection{Well-typed syntax}\label{sec:Def-wt}

As a warmup for the real description of the language Def, we look at
its well-typed description which does not include equations.

To obtain well-typed terms, we have to keep track not only of the
maximal number of free variables that can occur in a term but also of
their types. Thus we have a new sort of \emph{contexts} which is a
list of types. The empty context \verb$◇$ denotes no free variables,
the context \verb$◇ ▹ A ▹ B ▹ C$ has length three and the variables
\verb$v0$, \verb$v1$, \verb$v2$ have types \verb$C$, \verb$B$ and
\verb$A$, respectively. Variables (and terms) are now indexed by their
context and their type. The well-typed De Bruijn indices are recovered
as follows.

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module DefWT where

open import Lib hiding (_∘_)
module I where
  data Ty   : Set where
    Nat     : Ty
    Bool    : Ty
    
  data Con : Set where
    ◇   : Con
    _▹_ : Con → Ty → Con

  infixl 5 _▹_
  infixl 6 _+o_

  data Var : Con → Ty → Set where
    vz : ∀{Γ A} → Var (Γ ▹ A) A
    vs : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A

  data Tm (Γ : Con) : Ty → Set where
    var     : ∀{A} → Var Γ A → Tm Γ A
    def     : ∀{A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B

    true    : Tm Γ Bool
    false   : Tm Γ Bool
    ite     : ∀{A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
    num     : ℕ → Tm Γ Nat
    isZero  : Tm Γ Nat → Tm Γ Bool
    _+o_    : Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
  
  VarConstraint : (Γ : Con)(A : Ty)(n : ℕ) → Set
  VarConstraint ◇ _ n = Lift ⊥
  VarConstraint (Γ ▹ B) A zero = Lift (B ≡ A)
  VarConstraint (Γ ▹ B) A (suc n) = VarConstraint Γ A n
  
  private
    v' : (n : ℕ){Γ : Con}{A : Ty}⦃ proof : VarConstraint Γ A n ⦄ → Var Γ A
    v' zero {bc@(_ ▹ _)} {A} ⦃ mk proof ⦄ = transp (λ e → Var bc e) proof vz
    v' (suc n) {Γ ▹ _} {A} ⦃ proof ⦄ = vs (v' n {Γ} {A} ⦃ proof ⦄)
  
  v : (n : ℕ){Γ : Con}{A : Ty}⦃ proof : VarConstraint Γ A n ⦄ → Tm Γ A
  v n {Γ} {A} ⦃ p ⦄ = var (v' n {Γ} {A} ⦃ p ⦄)

  {-
  private
    Var' : ℕ → Con → Ty → Set
    Var' zero Γ A = Var Γ A
    Var' (suc n) Γ A = ∀ {B} → Var' n (Γ ▹ B) A

    Tm' : ℕ → Con → Ty → Set
    Tm' zero Γ A = Tm Γ A
    Tm' (suc n) Γ A = ∀ {B} → Tm' n (Γ ▹ B) A

    vs' : (n : ℕ) {Γ : Con} {A B : Ty} → Var' n Γ A → Var' n (Γ ▹ B) A
    vs' zero x = vs x
    vs' (suc n) x = vs' n x

    var' : (n : ℕ) {Γ : Con} {A : Ty} → Var' n Γ A → Tm' n Γ A
    var' zero x = var x
    var' (suc n) x = var' n x

    v' : (n : ℕ) {Γ : Con} {A : Ty} → Var' n (Γ ▹ A) A
    v' zero = vz
    v' (suc n) = vs' n (v' n)

  v : (n : ℕ) {Γ : Con} {A : Ty} → Tm' n (Γ ▹ A) A
  v n = var' n (v' n)
  -}
\end{code}
\begin{code}
  v0 : {Γ : Con}{A : Ty}        → Tm (Γ ▹ A) A
  v0 = v 0
  v1 : {Γ : Con}{A B : Ty}      → Tm (Γ ▹ A ▹ B) A
  v1 = v 1
  v2 : {Γ : Con}{A B C : Ty}    → Tm (Γ ▹ A ▹ B ▹ C) A
  v2 = v 2
  v3 : {Γ : Con}{A B C D : Ty}  → Tm (Γ ▹ A ▹ B ▹ C ▹ D) A
  v3 = var (vs (vs (vs vz)))
  v4 : {Γ : Con}{A B C D E : Ty}  → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E) A
  v4 = var (vs (vs (vs (vs vz))))
\end{code}
A DefWT model has the following components.
\begin{code}
record Model {i j k l} : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  infixl 5 _▹_
  infixl 6 _+o_
  field
    Ty      : Set i
    Nat     : Ty
    Bool    : Ty
    
    Con     : Set j
    ◇       : Con
    _▹_     : Con → Ty → Con

    Var     : Con → Ty → Set k
    vz      : ∀{Γ A} → Var (Γ ▹ A) A
    vs      : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A

    Tm      : Con → Ty → Set l
    var     : ∀{Γ A}    → Var Γ A → Tm Γ A
    def     : ∀{Γ A B}  → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
    true    : ∀{Γ}      → Tm Γ Bool
    false   : ∀{Γ}      → Tm Γ Bool
    ite     : ∀{Γ A}    → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
    num     : ∀{Γ}      → ℕ → Tm Γ Nat
    isZero  : ∀{Γ}      → Tm Γ Nat → Tm Γ Bool
    _+o_    : ∀{Γ}      → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
\end{code}
\begin{code}[hide]
  ⟦_⟧T : I.Ty → Ty
  ⟦ I.Nat   ⟧T = Nat
  ⟦ I.Bool  ⟧T = Bool

  ⟦_⟧C : I.Con → Con
  ⟦ I.◇      ⟧C = ◇
  ⟦ Γ I.▹ A  ⟧C = ⟦ Γ ⟧C ▹ ⟦ A ⟧T

  ⟦_⟧v : ∀{Γ A} → I.Var Γ A → Var ⟦ Γ ⟧C ⟦ A ⟧T
  ⟦ I.vz    ⟧v = vz
  ⟦ I.vs x  ⟧v = vs ⟦ x ⟧v

  ⟦_⟧t : ∀{Γ A} → I.Tm Γ A → Tm ⟦ Γ ⟧C ⟦ A ⟧T
  ⟦ I.var x         ⟧t = var ⟦ x ⟧v
  ⟦ I.def t t'      ⟧t = def ⟦ t ⟧t ⟦ t' ⟧t
  ⟦ I.num n         ⟧t = num n
  ⟦ I.isZero t      ⟧t = isZero ⟦ t ⟧t
  ⟦ t I.+o t'       ⟧t = ⟦ t ⟧t +o ⟦ t' ⟧t
  ⟦ I.true          ⟧t = true
  ⟦ I.false         ⟧t = false
  ⟦ I.ite t t' t''  ⟧t = ite ⟦ t ⟧t ⟦ t' ⟧t ⟦ t'' ⟧t
\end{code}
The derivation rule style presentation of the new operators:
\[
\infer{\texttt{vz : Var (Γ ▹ A) A}}{} \hspace{2em}
\infer{\texttt{vs x : Var (Γ ▹ B) A}}{\texttt{x : Var Γ A}} \hspace{2em}
\infer{\texttt{var x : Tm Γ A}}{\texttt{x : Var Γ A}} \hspace{2em}
\infer{\texttt{def t u : Tm Γ B}}{\texttt{u : Tm Γ A} && \texttt{t : Tm (Γ ▹ A) B}}
\]
Two example derivations:
{\footnotesize
\[
\infer{\texttt{def (isZero (num 0)) (ite (var vz) (num 0) (num 1)) : Tm ◇ Nat}}
  {\infer{\texttt{isZero (num 0) : Tm ◇ Bool}}{\infer{\texttt{num 0 : Tm ◇ Nat}}{}} &&
  \infer{\texttt{ite (var vz) (num 0) (num 1) : Tm (◇ ▹ Bool) Nat}}
    {\infer{\texttt{var vz : Tm (◇ ▹ Bool) Bool}}{\infer{\texttt{vz : Var (◇ ▹ Bool) Bool}}{}} &&
    \infer{\texttt{num 0 : Tm (◇ ▹ Bool) Nat}}{} && \infer{\texttt{num 1 : Tm (◇ ▹ Bool) Nat}}{}}}
\]
\[
\infer{\texttt{def (num 2) (def (var vz) (isZero (var vz + var (vs vz)))) : Tm ◇ Bool}}
  {\infer{\texttt{num 2 : Tm ◇ Nat}}{} &&
  \infer{\texttt{def (var vz) (isZero (var vz + var (vs vz))) : Tm (◇ ▹ Nat) Bool}}
    {\infer{\texttt{var vz : Tm (◇ ▹ Nat) Nat}}{\infer{\texttt{vz : Var (◇ ▹ Nat) Nat}}{}} &&
    \infer{\texttt{isZero (var vz + var (vs vz)) : Tm (◇ ▹ Nat ▹ Nat) Bool}}
      {\infer{\texttt{var vz + var (vs vz) : Tm (◇ ▹ Nat ▹ Nat) Nat}}
        {\infer{\texttt{var vz : Tm (◇ ▹ Nat ▹ Nat) Nat}}{\infer{\texttt{vz : Var (◇ ▹ Nat ▹ Nat) Nat}}{}} &&
        \infer{\texttt{var (vs vz) : Tm (◇ ▹ Nat ▹ Nat) Nat}}
          {\infer{\texttt{vs vz : Var (◇ ▹ Nat ▹ Nat) Nat}}{\infer{\texttt{vz : Var (◇ ▹ Nat) Nat}}{}}}}}}}
\]}

\begin{code}[hide]
St : Model
St = record
  { Ty     = Set
  ; Nat    = ℕ
  ; Bool   = 𝟚
  ; Con    = Set
  ; ◇      = Lift ⊤
  ; _▹_    = _×_
  ; Var    = λ Γ A → Γ → A
  ; vz     = π₂
  ; vs     = λ x γ → x (π₁ γ)
  ; Tm     = λ Γ A → Γ → A
  ; var    = λ x → x
  ; def    = λ u t γ → t (γ , u γ)
  ; num    = λ n γ → n
  ; isZero = λ t γ → iteℕ tt (λ _ → ff) (t γ) 
  ; _+o_   = λ u v γ → u γ + v γ
  ; true   = λ γ → tt
  ; false  = λ γ → ff
  ; ite    = λ t u v γ → if t γ then u γ else v γ
  }

module St = Model St
\end{code}

\begin{exe}[compulsory]
  Derive \verb$def (var vz) true : Tm (◇ ▹ Nat) Bool$!
\end{exe}
\begin{exe}[compulsory]
  Derive \verb$def (var (vs vz)) (var vz) : Tm (◇ ▹ Bool ▹ Nat) Bool$!
\end{exe}
\begin{exe}[compulsory]
  Derive \verb$def (num 1) (var vz + var (vs vz)) : Tm (◇ ▹ Nat) Nat$!
\end{exe}
\begin{exe}[compulsory]
  What can be \verb$t$ such that \verb$def t (def true (ite v0 v1 v1)) : Tm ◇ Nat$?
\end{exe}
