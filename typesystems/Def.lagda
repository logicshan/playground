\subsection{Well-typed syntax with equations}
\label{sec:def}

If we have local definitions, then in addition to equations such as \verb$isZero (num 0) = true$,
we need equations like the following.
\begin{verbatim}
def u (v0 + v0) = u + u
def u (def u' (v0 + v1)) = u' + u
def u (def u' (v1 + (v0 + (v1 + num 3)))) = u + (u' + (u + num 3))
\end{verbatim}
In general, we would like to have \verb$def u t = t [ ⟨ u ⟩ ]$ where
\verb$t [ ⟨ u ⟩ ]$ is the same as \verb$t$, but all \verb$v0$s are replaced
by \verb$u$, all \verb$v1$s are replaced by \verb$v0$s, all \verb$v2$s
are replaced by \verb$v1$s, and so on.

As a first try we add a new operation \verb$_[_]₀$ which instantiates the last variable (\verb$v0$) with a term:
\[
\infer{\texttt{t [ w ]₀ : Tm Γ A}}{\texttt{t : Tm (Γ ▹ B) A} && \texttt{w : Tm Γ B}} \hspace{4em}
\]
and we add the following equations
\begin{verbatim}
var vz [ w ]₀ = w
var (vs x) [ w ]₀ = var x
true [ w ]₀ = true
false [ w ]₀ = false
ite t u v [ w ]₀ = ite (t [ w ]₀) (u [ w ]₀) (v [ w ]₀)
num n [ w ]₀ = num n
isZero t [ w ]₀ = isZero (t [ w ]₀)
u +o v [ w ]₀ = (u [ w ]₀) +o (v [ w ]₀)
\end{verbatim}
which are called substitution laws (instantiation is sometimes called
substitution). They explain that the operation \verb$_[_]₀$ computes
by looking at the shape of the term that is being instantiated. This is
like defining instantiation by iteration on the term. But how do we
instantiate a term that is a local definition?
\[
\infer{\texttt{def t t' [ w ]₀ = def (t [ w ]₀) (t' [ ? ]₀)}}{\texttt{t : Tm (Γ ▹ C) A} && \texttt{t' : Tm (Γ ▹ C ▹ A) B} && \texttt{w : Tm Γ C}}
\]
The issue is that in \verb$t'$ we need to instantiate the last but one variable, not
the last one. We have to generalise \verb$_[_]₀$.

We introduce a new sort called substitutions \verb$Sub Δ Γ$ for any two
context \verb$Δ$ and \verb$Γ$. \verb$Sub Δ Γ$ depends on \verb$Δ$ just
as \verb$Tm Δ A$, however it provides not only one term of type \verb$A$,
but one term for each type in the context \verb$Γ$. We use \verb$σ$, \verb$ρ$
metavariables for substitutions. The first way to create such a
substitution is \verb$⟨_⟩$ which turns a term \verb$Tm Γ A$ into
\verb$Sub Γ (Γ ▹ A)$.
\[
\infer{\texttt{Sub : Con → Con → Set}}{} \hspace{4em}
\infer{\texttt{t [ σ ] : Tm Δ A}}{\texttt{t : Tm Γ A} &&
\texttt{σ : Sub Δ Γ}} \hspace{4em} \infer{\texttt{⟨ u ⟩ : Sub Γ (Γ ▹ A)}}{\texttt{u : Tm Γ A}}
\]
Then we need a way to lift a substitution so that it does not touch
the last variable:
\[
\infer{\texttt{σ ⁺ : Sub (Δ ▹ A) (Γ ▹ A)}}{\texttt{σ : Sub Δ Γ}}
\]
Now we can explain how to instantiate all terms:
\begin{verbatim}
true [ σ ] = true
false [ σ ] = false
ite t u v [ σ ] = ite (t [ σ ]) (u [ σ ]) (v [ σ ])
num n [ σ ] = num n
isZero t [ σ ] = isZero (t [ σ ])
u +o v [ σ ] = (u [ σ ]) +o (v [ σ ])
def t t' [ σ ] = def (t [ σ ]) (t' [ σ ⁺ ])
\end{verbatim}
In the last case we used lifting when instantiating \verb$t'$.
When instantiating variables, we have to check which way the
substitution was built.
\begin{verbatim}
var vz [ ⟨ w ⟩ ] = w
var vz [ σ ⁺ ] = var vz
var (vs x) [ ⟨ w ⟩ ] = var x
var (vs x) [ σ ⁺ ] = ?
\end{verbatim}
In the last case we have the following types.
\begin{verbatim}
x : Var Γ A
vs x : Var (Γ ▹ B) A
σ : Sub Δ Γ
σ ⁺ : Sub (Δ ▹ B) (Γ ▹ B)
var x [ σ ] : Tm Δ A
var (vs x) [ σ ⁺ ] : Tm (Δ ▹ B) A
\end{verbatim}
So we need to \emph{weaken} \verb$var x [ σ ]$ which is in context
\verb$Δ$ to obtain a term in context \verb$Δ ▹ B$. Weakening means
that we add one to every De Bruijn index. For this purpose we introduce
a new substitution \verb$p$ which we can now use to compute
\verb$var (vs x) [ σ ⁺ ]$ and then again we have to say what happens if
we instantiate a variable with \verb$p$, but that is easy.
\[
\infer{\texttt{p : Sub (Γ ▹ A) Γ}}{} \hspace{4em}
\infer{\texttt{var (vs x) [ σ ⁺ ] = var x [ σ ] [ p ]}}{} \hspace{4em}
\infer{\texttt{var x [ p ] = var (vs x)}}{}
\]

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module Def where

open import Lib

-- note: this is duplication of code but I don't know how to fix this easily
module tmp where
  record Model {i j} : Set (lsuc (i ⊔ j)) where
    infixl 6 _[_]
    infixl 5 _▹_
    infixl 7 _+o_

    field
\end{code}
In summary, a Def-model consists of the following components. We list them in groups.
\begin{itemize}
\item We have the following sorts.
\begin{code}
      Ty        : Set i
      Con       : Set i
      Var       : Con → Ty → Set j
      Tm        : Con → Ty → Set j
      Sub       : Con → Con → Set j
\end{code}
\item The rules of the \emph{substitution calculus} are the general rules concerning contexts,
substitutions and variables. They do not mention any specific types.
\begin{code}
      ◇         : Con
      _▹_       : Con → Ty → Con

      p         : ∀{Γ A} → Sub (Γ ▹ A) Γ
      ⟨_⟩       : ∀{Γ A} → Tm Γ A → Sub Γ (Γ ▹ A)
      _⁺        : ∀{Γ Δ A} → (σ : Sub Δ Γ) → Sub (Δ ▹ A) (Γ ▹ A)

      vz        : ∀{Γ A} → Var (Γ ▹ A) A
      vs        : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A
      var       : ∀{Γ A} → Var Γ A → Tm Γ A
      _[_]      : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
      [p]       : ∀{Γ A B x} →      var {Γ}{A} x [ p {A = B} ] ≡ var (vs x)
      vz[⟨⟩]    : ∀{Γ A t} →        var (vz {Γ}{A}) [ ⟨ t ⟩ ] ≡ t
      vz[⁺]     : ∀{Γ Δ A σ} →      var (vz {Γ}{A}) [ σ ⁺ ] ≡ var (vz {Δ}{A})
      vs[⟨⟩]    : ∀{Γ A B x t} →    var (vs {Γ}{A}{B} x) [ ⟨ t ⟩ ] ≡ var x
      vs[⁺]     : ∀{Γ Δ A B x σ} →  var (vs {Γ}{A}{B} x) [ σ ⁺ ] ≡ var x [ σ ] [ p {Δ} ]
\end{code}
\item The rules for the type \verb$Bool$ are the following.
\begin{code}
      Bool      : Ty
      true      : ∀{Γ} → Tm Γ Bool
      false     : ∀{Γ} → Tm Γ Bool
      ite       : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
      iteβ₁     : ∀{Γ A u v} → ite {Γ}{A} true  u v ≡ u
      iteβ₂     : ∀{Γ A u v} → ite {Γ}{A} false u v ≡ v
      true[]    : ∀{Γ Δ σ} → true  {Γ} [ σ ] ≡ true  {Δ}
      false[]   : ∀{Γ Δ σ} → false {Γ} [ σ ] ≡ false {Δ}
      ite[]     : ∀{Γ Δ A t u v σ} → (ite {Γ}{A} t u v) [ σ ] ≡ ite {Δ} (t [ σ ]) (u [ σ ]) (v [ σ ])
\end{code}
\item The rules for the type \verb$Nat$ are the following.
\begin{code}
      Nat       : Ty
      num       : ∀{Γ} → ℕ → Tm Γ Nat
      isZero    : ∀{Γ} → Tm Γ Nat → Tm Γ Bool
      _+o_      : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
      isZeroβ₁  : ∀{Γ} → isZero (num 0) ≡ true {Γ = Γ}
      isZeroβ₂  : ∀{Γ n} → isZero (num (1 + n)) ≡ false {Γ = Γ}
      +β        : ∀{Γ m n} → num m +o num n ≡ num {Γ = Γ} (m + n)
      num[]     : ∀{Γ Δ σ n} → num {Γ} n [ σ ] ≡ num {Δ} n
      isZero[]  : ∀{Γ Δ t σ} → (isZero {Γ} t) [ σ ] ≡ isZero {Δ} (t [ σ ])
      +[]       : ∀{Γ Δ u v}{σ : Sub Δ Γ} → (u +o v) [ σ ] ≡ (u [ σ ]) +o (v [ σ ])
\end{code}
\end{itemize}
In fact, we haven't added the operator \verb$def$ to our language. But as it
has a simple computation rule, we can just define it as \emph{syntactic sugar}
(an abbreviation).
\begin{code}
    def : ∀{Γ A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
    def u t = t [ ⟨ u ⟩ ]
\end{code}
\begin{code}[hide]
import Def.Syntax
import Def.DepModel
open import Def.Model
import Def.ParaModel
\end{code}
The term \verb$let x:= false in if x then true else isZero (if x then (num 0) else (num 1))$ is equal to \verb$false$ in any model.
\begin{code}[hide]
module Example {i}{j}(M : Model {i}{j}) where
  open Model M
  pt : def false (ite (var vz) true (isZero (ite (var vz) (num 0) (num 1)))) ≡ false {◇}
  pt =
\end{code}
\begin{code}
    def false (ite (var vz) true (isZero (ite (var vz) (num 0) (num 1))))
      ≡⟨ refl ⟩
    ite (var vz) true (isZero (ite (var vz) (num 0) (num 1))) [ ⟨ false ⟩ ]
      ≡⟨ ite[] ⟩
    ite ((var vz) [ ⟨ false ⟩ ]) (true [ ⟨ false ⟩ ]) (isZero (ite (var vz) (num 0) (num 1)) [ ⟨ false ⟩ ])
      ≡⟨ cong (λ z → ite z (true [ ⟨ false ⟩ ]) (isZero (ite (var vz) (num 0) (num 1)) [ ⟨ false ⟩ ])) vz[⟨⟩] ⟩
    ite false (true [ ⟨ false ⟩ ]) (isZero (ite (var vz) (num 0) (num 1)) [ ⟨ false ⟩ ])
      ≡⟨ iteβ₂ ⟩
    isZero (ite (var vz) (num 0) (num 1)) [ ⟨ false ⟩ ]
      ≡⟨ isZero[] ⟩
    isZero (ite (var vz) (num 0) (num 1) [ ⟨ false ⟩ ])
      ≡⟨ cong isZero ite[] ⟩
    isZero (ite (var vz [ ⟨ false ⟩ ]) (num 0 [ ⟨ false ⟩ ]) (num 1 [ ⟨ false ⟩ ]))
      ≡⟨ cong (λ z → isZero (ite z (num 0 [ ⟨ false ⟩ ]) (num 1 [ ⟨ false ⟩ ]))) vz[⟨⟩] ⟩
    isZero (ite false (num 0 [ ⟨ false ⟩ ]) (num 1 [ ⟨ false ⟩ ]))
      ≡⟨ cong isZero iteβ₂ ⟩
    isZero (num 1 [ ⟨ false ⟩ ])
      ≡⟨ cong isZero num[] ⟩
    isZero (num 1)
      ≡⟨ isZeroβ₂ ⟩
    false
      ∎
\end{code}

A \emph{program} of type \verb$A$ is an element of \verb$I.Tm ◇ A$
where \verb$I$ is the initial model as usual. When we work ``inside''
the language, we can only write programs.

% 1. prove t[p][<u>] = t: first derive for vars, then prove it for terms by induction
% 2. prove t[<u>][σ] = t[σ⁺][<u[σ]>], case distinction for vars, induction for terms
% now we can do the exercise

\begin{exe}[compulsory]
Prove \verb$(def t u) [ σ ] ≡ def (t [ σ ]) (u [ σ ⁺ ])$ for any \verb$t$, \verb$u$, \verb$γ$ in the syntax.
\end{exe}

\subsubsection{Standard model and inequalities in the empty context}

In the standard model, types are sets as before, contexts are iterated
products of their constituent types, so they are also sets. Terms are
not simply elements of their types because they depend on a
context. This dependency is modelled using functions: a term of
type \verb$A$ in context \verb$Γ$ is a function \verb$Γ → A$. Substitutions are also functions.
\begin{code}
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
\end{code}
A term in the empty context reproduces the interpretation of terms in
the standard model of Razor, e.g.\ \verb$Tm ◇ Nat = ⊤ → ℕ$ which is
equivalent to having a natural number. All equations hold by
definition in the standard model: we can simply prove them by
\verb$refl$.

Equational consistency can be proved using the standard model just as
for Razor. For example, we can show that the following two closed
terms are not equal in the syntax. If they were equal, then their
interpretations into the standard model would be also equal.
\begin{code}
import Def.Syntax as I

not-equal : ¬ (
  I.ite (I.isZero (I.num 2)) (I.num 3) (I.num 12) ≡
  I.ite (I.isZero (I.num 0 I.+o I.num 0)) (I.num 11) (I.num {I.◇} 3))
not-equal e = 12≠11 (cong (λ t → St.⟦ t ⟧t (mk triv)) e)
  where
    12≠11 : ¬ (12 ≡ 11)
    12≠11 ()
\end{code}
For open terms, the standard model is not good enough for the same purpose. From normalisation, we will obtain that
\verb$isZero (q {◇} +o num 2)$ is not equal in the syntax to \verb$false$, but in the standard
model they are both interpreted by the constant false function.
\begin{code}
ex-open : St.⟦ I.isZero (I.var (I.vz {I.◇}) I.+o I.num 2) ⟧t ≡ St.⟦ I.false {I.◇ I.▹ I.Nat} ⟧t
ex-open = funext λ { (_ , n) → cong (iteℕ tt (λ _ → ff)) (+comm {n}{2}) }
\end{code}

\subsubsection{Type inference}

We define type inference from ABT-level trees to well-typed trees just
as for Razor (Section \ref{sec:razor-infer}). We define a DefABT model
built out of Def syntax. We use an Agda trick called ``views'' 
\cite{DBLP:conf/afp/Norell08} to connect contexts and their lengths.
\begin{code}
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
\end{code}
The final \verb$infer$ function works on terms in the empty context.
\begin{code}
infer : DefABT.I.Tm 0 → Maybe (Σ I.Ty λ A → I.Tm I.◇ A)
infer pt = Inf.⟦ pt ⟧t nil
\end{code}

\subsubsection{Normalisation}
\label{sec:def-normalisation}

Before defining normal forms we group the operators specific to \verb$Bool$ and \verb$Nat$ as follows:
\begin{itemize}
\item constructors (introduction rules): operators which introduce elements of the type (\verb$true$ and \verb$false$ for \verb$Bool$; \verb$num$ for \verb$Nat$),
\item destructors (elimination rules, eliminators): operators that can be used to eliminate an element of the type (\verb$ite$ for \verb$Bool$; \verb$isZero$ and \verb$_+o_$ for \verb$Nat$),
\item computation (\verb$β$) rules: equations that explain what happens if a destructor is applied to a constructor (\verb$iteβ₁$ and \verb$iteβ₂$ for \verb$Bool$; \verb$isZeroβ₁$, \verb$isZeroβ₂$ and \verb$+β$ for \verb$Nat$),
\item uniqueness (\verb$η$) rules: equations that explain what happens if a constructor is applied to a destructor (we don't have any),
\item substitution rules: explain how instantiation \verb$_[_]$ interacts with the operators (\verb$true[]$, \verb$false[]$, \verb$ite[]$, \verb$num[]$, \verb$isZero[]$, \verb$+[]$).
\end{itemize}
Perhaps surprisingly, \verb$isZero$ is a destructor (of \verb$Nat$) instead of a constructor (of \verb$Bool$). This is because it computes depending on its input which is a \verb$Nat$.

Each destructor has some \emph{main arguments} (scrutinees). These are the arguments which are in constructor forms in the
computation rule. The main argument of \verb$ite$ is the first one, the single argument of \verb$isZero$ is a main
argument, and both arguments of \verb$_+o_$ are main. Once we know the main arguemnts, we can compute further using the \verb$β$ rule.

Neutral terms and normal forms are defined as mutual inductive types.
\begin{code}[hide]
open I

infixl 6 _[_]V _[_]Ne _[_]Nf
infixl 7 _+NeNe_ _+NeNf_ _+NfNe_ _+NfNf_
\end{code}
\begin{code}
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
\end{code}
Neutral terms are either variables or a destructor with a neutral main
argument. For example, \verb$ite (var vz) true true$ is a neutral term
because we don't know which computation rule (\verb$iteβ₁$ or
\verb$iteβ₂$) to apply.  Normal forms are either neutral terms or
constructors. All non-main arguments of destructors and arguments of
constructors have to be normal (we don't have any of the latter). The
destructor \verb$_+_$ has two main arguments, at least one of them has
to be neutral. That is why we have three cases: both are neutral, the
left is normal (that is, a natural number because that is the only
parameter of \verb$num$), the right is normal.  For example, \verb$num 3 +o var vz$
and \verb$num 3 +o ite (var vz) (num 1) (num 2)$ are neutral (and
hence normal), but \verb$num 3 +o num 2$ is not normal because by
\verb$+β$ it is equal to \verb$num 5$.

Normal forms can be quoted back into the syntax.
\begin{code}
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
\end{code}

\begin{exe}
What is the normal form of the following terms?
\begin{code}
t1 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ v0 +o (num 1 +o num 2)
t2 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ v0 +o v0
t3 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ (num 1 +o num 2) +o v0
t4 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ (num 1 +o v0) +o v0
t5 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ isZero (num 2)
t6 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ isZero (num 1 +o num 2)
t7 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ isZero (num 1 +o v0)
t8 : Σsp (Nf ◇ Bool) λ v → ⌜ v ⌝Nf ≡ def (num 0) (def (isZero v0) (ite v0 false true))
\end{code}
\begin{code}[hide]
t1 = exercise
t2 = exercise
t3 = exercise
t4 = exercise
t5 = exercise
t6 = exercise
t7 = exercise
t8 = exercise
\end{code}
\end{exe}

In contrast with Razor (Section \ref{sec:razor-norm}) where we were
able to normalise using the standard model, for Def we have to define
a separate model for normalisation.  Terms in this model will be
normal forms and substitutions will be either weakenings (\verb$p$
with some \verb$_⁺$s applied to it) or single substitutions (for a \verb$t$ normal, \verb$⟨ t ⟩$
with some \verb$_⁺$s applied to it). We
first define these together with their respective quote functions.
\begin{code}
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
\end{code}
Now we define the interpretation of the destructors on normal
forms. They return the neutral term when given a neutral argument, and
follow the computation rule when given a constructor.
\begin{code}
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
\end{code}
Instantiation of normal forms by weakenings and single normal subsitutions.
\begin{code}
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
\end{code}
Now we define general normal substitutions: it is either a weakening or a single
normal substitution.
\begin{code}
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
\end{code}
Instantiation with general normal substitutions.
\begin{code}
_[_]V : ∀{Γ A} → Var Γ A → ∀{Δ} → SubNf Δ Γ → Nf Δ A
x [ ι₁ σ ]V = neu (varNe (x [ σ ]VWk))
x [ ι₂ σ ]V = x [ σ ]VSub1

_[_]Ne : ∀{Γ A} → Ne Γ A → ∀{Δ} → SubNf Δ Γ → Nf Δ A
t [ ι₁ σ ]Ne = neu (t [ σ ]NeWk)
t [ ι₂ σ ]Ne = t [ σ ]NeSub1

_[_]Nf : ∀{Γ A} → Nf Γ A → ∀{Δ} → SubNf Δ Γ → Nf Δ A
t [ ι₁ σ ]Nf = t [ σ ]NfWk
t [ ι₂ σ ]Nf = t [ σ ]NfSub1
\end{code}
We prove the substitution laws by case analysis on general normal substitutions and
the main arguments.
\begin{code}
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
\end{code}
\begin{code}[hide]
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
\end{code}
Now we build the model for normalisation.
\begin{code}
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
\end{code}
Normalisation is interpretation into this model.
\begin{code}
norm : ∀{Γ A} → Tm Γ A → Nf Γ A
norm = N.⟦_⟧t
\end{code}
Some examples of normalisation:
\begin{code}
ex1 : norm (ite (isZero (num 1 +o num 2)) (v 0) false) ≡ falseNf {◇ ▹ Bool}
ex1 = refl

ex2 : norm (def (num 1) ((v 0 +o v 0) +o ite false (v 0) (v 0))) ≡ numNf {◇} 3
ex2 = refl
\end{code}
We used the standard model to show that two closed terms are not equal in the syntax. We can also
use normalisation for the same purpose:
\begin{code}
not-equal' : ¬ (
  I.ite (I.isZero (I.num 2)) (I.num 3) (I.num 12) ≡
  I.ite (I.isZero (I.num 0 I.+o I.num 0)) (I.num 11) (I.num {I.◇} 3))
not-equal' e = 12≠11 (cong norm e)
  where
    12≠11 : ¬ (numNf 12 ≡ numNf 11)
    12≠11 ()
\end{code}
And unlike the standard interpretation, normalisation can be used to prove inequality of open terms:
\begin{code}
ex-open' : ¬ (isZero (v 0 {◇ ▹ Nat} +o num 2) ≡ false)
ex-open' e with cong norm e
... | ()
\end{code}
For completeness, we first prove that the operations in the normalisation model commute with
quotation. These are proven by induction on the variable/neutral term/normal form and the
general normal substitution (see the source code for details).
\begin{code}
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
\end{code}
\begin{code}[hide]
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
\end{code}
Now we build the dependent model for completeness: completeness is proven
by induction on terms and substitutions.
\begin{code}
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
\end{code}
We can use completeness to show that two terms are equal without doing all the complex equational
reasoning. 
\begin{code}
e4 : ite true (num 3 +o num 2) (num 0) ≡ num 1 +o (num 2 +o (num 1 +o num {◇} 1))
e4 =
  ite true (num 3 +o num 2) (num 0)
                                     ≡⟨ compl (ite true (num 3 +o num 2) (num 0)) ⁻¹ ⟩
  num 5
                                     ≡⟨ compl (num 1 +o (num 2 +o (num 1 +o num 1))) ⟩
  num 1 +o (num 2 +o (num 1 +o num 1))
                                     ∎
\end{code}
Stability of normalisation (there is no junk in normal forms) is proved by induction on
variables, neutral terms and normal forms.
\begin{code}
\end{code}
\begin{code}
stabNe : ∀{Γ A}(t : Ne Γ A) → norm ⌜ t ⌝Ne ≡ neu t
stabNf : ∀{Γ A}(t : Nf Γ A) → norm ⌜ t ⌝Nf ≡ t
\end{code}
\begin{code}[hide]
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
\end{code}

\begin{code}[hide]
infix 4 _≟ℕ_ _≟Ty_ _≟Var_ _≟Ne_ _≟Nf_ _≟Tm_ 
\end{code}
Decidability of equality of normal forms. We show how we do it for natural numbers, the
rest of the proofs are analogous (see the source code).
\begin{code}
_≟ℕ_ : (m n : ℕ) → Dec (Lift (m ≡ n))
zero  ≟ℕ zero    = ι₁ (mk refl)
zero  ≟ℕ suc n   = ι₂ (mk λ { (mk ()) })
suc m ≟ℕ zero    = ι₂ (mk λ { (mk ()) })
suc m ≟ℕ suc n   with m ≟ℕ n
... | ι₁ (mk e)  = ι₁ (mk (cong suc e))
... | ι₂ f       = ι₂ (mk λ { (mk refl) → un f (mk refl)})
\end{code}
\begin{code}
_≟Ty_ : (A B : Ty) → Dec (Lift (A ≡ B))
\end{code}
\begin{code}[hide]
Bool  ≟Ty Bool  = ι₁ (mk refl)
Bool  ≟Ty Nat   = ι₂ (mk λ { (mk ()) })
Nat   ≟Ty Nat   = ι₁ (mk refl)
Nat   ≟Ty Bool  = ι₂ (mk λ { (mk ()) })
\end{code}
\begin{code}
_≟Var_ : ∀{Γ A₀ A₁}(x₀ : Var Γ A₀)(x₁ : Var Γ A₁) →
  Dec (Σ (Lift (A₀ ≡ A₁)) λ e → Lift (transp (Var Γ) (un e) x₀ ≡ x₁))
\end{code}
\begin{code}[hide]
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

\end{code}
\begin{code}
_≟Ne_ : ∀{Γ A₀ A₁}(a₀ : Ne Γ A₀)(a₁ : Ne Γ A₁) →
  Dec (Σ (Lift (A₀ ≡ A₁)) λ e → Lift (transp (Ne Γ) (un e) a₀ ≡ a₁))
_≟Nf_ : ∀{Γ A}(a₀ a₁ : Nf Γ A) → Dec (Lift (a₀ ≡ a₁))
\end{code}
\begin{code}[hide]
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
\end{code}
We obtain decidability of equality for all terms by checking whether the
normal forms are equal. If they are, then by completenes, we have an equality between the
two terms. If they are not equal, then if the terms were equal then their normal forms would be
also equal, which is a contradiction.
\begin{code}
_≟Tm_ : ∀{Γ A}(t₀ t₁ : Tm Γ A) → Dec (Lift (t₀ ≡ t₁))
t₀ ≟Tm t₁ with norm t₀ ≟Nf norm t₁
... | ι₁ (mk e) = ι₁ (mk (compl t₀ ⁻¹ ◾ cong ⌜_⌝Nf e ◾ compl t₁))
... | ι₂ f = ι₂ (mk λ t₀₁ → un f (mk (cong norm (un t₀₁))))
\end{code}
Now it is very easy to prove equalities in the syntax. If we know that a witness of
decidability is \verb$ι₁$ by definition, then we can extract the witness from decidability of
equality.
\begin{code}
ex3 : isZero (v 0 +o num 2) [ ⟨ num {◇} 0 ⟩ ] ≡ false
ex3 = extract (isZero (v 0 +o num 2) [ ⟨ num {◇} 0 ⟩ ] ≟Tm false)
\end{code}
If we know that it is \verb$ι₂$ by definition, we can use \verb$extract'$ to obtain falsity:
\begin{code}
ex-open'' : ¬ (isZero (var (vz {◇}) +o num 2) ≡ false)
ex-open'' = extract' (isZero (var vz +o num 2) ≟Tm false)
\end{code}

From normalisation it follows that constructors are disjoint and
injective, but not destructors.

\begin{code}
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
\end{code}

\subsubsection{A sort of first order functions}
\label{sec:def-firstorder}

The language Def has a separate sort of first-order functions: in
context \verb$Γ$ functions from \verb$A$ to \verb$B$ aredenoted
\verb$Fun A B$. We have a lambda and an application operator. All of
this is syntactic sugar (just like local definitions).

\begin{code}[hide]
infixl 5 _$_
\end{code}
\begin{code}
Fun : Con → Ty → Ty → Set
Fun Γ A B = Tm (Γ ▹ A) B

lam : ∀{Γ A B} → Tm (Γ ▹ A) B → Fun Γ A B
lam t = t

_$_ : ∀{Γ A B} → Fun Γ A B → Tm Γ A → Tm Γ B
t $ u = t [ ⟨ u ⟩ ]
\end{code}
