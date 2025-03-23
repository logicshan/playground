\section{Well-typed syntax}

The abstract syntax tree description of Razor still contains
meaningless programs, e.g.\ \verb$isZero true$ or \verb$true + num 2$.
The problem is that \verb$isZero$ expects a natural number and
not a boolean and \verb$+$ expects two natural numbers. The solution
is to add the type information to the terms, that is, whether a term
is a boolean or a natural number.

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module RazorWT where

open import Lib

module I where
  infixl 7 _+o_
  data Ty   : Set where
    Nat     : Ty
    Bool    : Ty
  data Tm   : Ty → Set where
    true    : Tm Bool
    false   : Tm Bool
    ite     : {A : Ty} → Tm Bool → Tm A → Tm A → Tm A
    num     : ℕ → Tm Nat
    isZero  : Tm Nat → Tm Bool
    _+o_    : Tm Nat → Tm Nat → Tm Nat
\end{code}

The language RazorWT (well-typed) contains two sorts: \verb$Ty$ and \verb$Tm$,
and the latter sort is indexed by the first one. 
A RazorWT model is a record with the following components.
\begin{code}
record Model {ℓ ℓ'} : Set (lsuc (ℓ ⊔ ℓ')) where
  field
    Ty      : Set ℓ
    Tm      : Ty → Set ℓ'
    Nat     : Ty
    Bool    : Ty
    true    : Tm Bool
    false   : Tm Bool
    ite     : {A : Ty} → Tm Bool → Tm A → Tm A → Tm A
    num     : ℕ → Tm Nat
    isZero  : Tm Nat → Tm Bool
    _+o_    : Tm Nat → Tm Nat → Tm Nat
\end{code}

There is no set of terms anymore, but there is a set of
\verb$Nat$-terms and a set of \verb$Bool$-terms, separately. Each
operator expects a term of the correct type as input and returns a
term of the appropriate type. For example, the first argument of
\verb$ite$ has to be a boolean and the second and third arguments have
to be of the same type. The type of \verb$ite t u v $ is the same as
the type of the second and third arguments. This type is an
\emph{implicit argument} of \verb$ite$ which we omit for readability
(the full type would be \verb$(A : Ty) → Tm Bool → Tm A → Tm A → Tm A$,
now it is \verb${A : Ty} → Tm Bool → Tm A → Tm A → Tm A$).

We could have used two sorts, \verb$TmBool$ and \verb$TmNat$ instead
however that would not generalise to other type formers such as lists
where we would need infinitely many sets of terms.

The syntax of RazorWT is still called \verb$I$ and its iterator
consists of two functions (one for each sort, denoted by
\verb$⟦_⟧T$ and \verb$⟦_⟧t$) which preserve all operations.
\begin{code}
  ⟦_⟧T  : I.Ty → Ty
  ⟦_⟧t  : ∀{A} → I.Tm A → Tm ⟦ A ⟧T
  ⟦ I.Nat           ⟧T = Nat
  ⟦ I.Bool          ⟧T = Bool
  ⟦ I.true          ⟧t = true
  ⟦ I.false         ⟧t = false
  ⟦ I.ite t u v     ⟧t = ite ⟦ t ⟧t ⟦ u ⟧t ⟦ v ⟧t
  ⟦ I.num n         ⟧t = num n
  ⟦ I.isZero t      ⟧t = isZero ⟦ t ⟧t
  ⟦ u I.+o v        ⟧t = ⟦ u ⟧t +o ⟦ v ⟧t
\end{code}

We also have a notion of dependent model and induction just as for \verb$RazorAST$.
\begin{code}
record DepModel {ℓ ℓ'} : Set (lsuc (ℓ ⊔ ℓ')) where
  field
    Ty∙      :  I.Ty → Set ℓ
    Tm∙      :  ∀{A} → Ty∙ A → I.Tm A → Set ℓ'
    Nat∙     :  Ty∙ I.Nat
    Bool∙    :  Ty∙ I.Bool
    true∙    :  Tm∙ Bool∙ I.true
    false∙   :  Tm∙ Bool∙ I.false
    ite∙     :  ∀{A t u v}{A∙ : Ty∙ A} → Tm∙ Bool∙ t → Tm∙ A∙ u → Tm∙ A∙ v →
                Tm∙ A∙ (I.ite t u v)
    num∙     :  (n : ℕ) → Tm∙ Nat∙ (I.num n)
    isZero∙  :  ∀{t} → Tm∙ Nat∙ t → Tm∙ Bool∙ (I.isZero t)
    _+o∙_    :  ∀{u v} → Tm∙ Nat∙ u → Tm∙ Nat∙ v → Tm∙ Nat∙ (u I.+o v)
  ⟦_⟧T  : (A : I.Ty) → Ty∙ A
  ⟦_⟧t  : ∀{A}(t : I.Tm A) → Tm∙ ⟦ A ⟧T t
  ⟦ I.Nat           ⟧T = Nat∙
  ⟦ I.Bool          ⟧T = Bool∙
  ⟦ I.true          ⟧t = true∙
  ⟦ I.false         ⟧t = false∙
  ⟦ I.ite t u v     ⟧t = ite∙ ⟦ t ⟧t ⟦ u ⟧t ⟦ v ⟧t
  ⟦ I.num n         ⟧t = num∙ n
  ⟦ I.isZero t      ⟧t = isZero∙ ⟦ t ⟧t
  ⟦ u I.+o v        ⟧t = ⟦ u ⟧t +o∙ ⟦ v ⟧t
\end{code}

An alternative notation for the syntax is the \emph{derivation rule}
style. Instead of
\begin{verbatim}
ite : {A : Ty} → Tm Bool → Tm A → Tm A → Tm A
\end{verbatim}
or even 
\begin{verbatim}
ite : {A : Ty}(t : Tm Bool)(u : Tm A)(v : Tm A) → Tm A
\end{verbatim}
we write
\[
\infer{\texttt{ite t u v : Tm A}}{\texttt{t : Tm Bool} && \texttt{u : Tm A} && \texttt{v : Tm A}}
\]
and similarly for the other rules. The horizontal line simply denotes function space. Now we can derive RazorWT terms by building \emph{derivation trees} in a bottom-up way. At each step we check whether the types match -- the tree has to be built in a well-typed way. The derivation of our example term
\begin{verbatim}
ite {Bool} (isZero (num 0 + num 1)) false (isZero (num 0))
\end{verbatim}
is depicted as follows.
\[
\infer{\texttt{ite (isZero (num 0 + num 1)) false (isZero (num 0)) : Tm Bool}}{\infer{\texttt{isZero (num 0 + num 1) : Tm Bool}}{\infer{\texttt{num 0 + num 1 : Tm Nat}}{\infer{\texttt{num 0 : Tm Nat}}{} && \infer{\texttt{num 1 : Tm Nat}}{}}} && \infer{\texttt{false : Tm Bool}}{} && \infer{\texttt{isZero (num 0) : Tm Bool}}{\infer{\texttt{num 0 : Tm Nat}}{}} }
\]

\begin{exe}[compulsory]
  Draw the derivation trees of the following terms.
  \begin{verbatim}
  isZero (num 1 + ite true (num 2) (num 3))
  isZero (num 1 + (num 2 + num 3))
  isZero ((num 1 + num 2) + num 3)
  ite (isZero (num 0)) (num 1 + num 2) (num 3)
  \end{verbatim}
\end{exe}
\begin{exe}[recommended]
  Implement the two different leaf count functions and using a dependent model show that they give the same result. See Section \ref{sec:razor-ast-ind}.
\end{exe}

\subsection{Type inference}
\label{sec:razor-infer}

The goal of type inference is to turn a syntactic RazorAST term into a
well-typed (RazorWT) term. The depiction of this process is that we
try to build a derivation tree, but we might fail at some point.

Precisely, we will use the RazorAST-iterator on a RazorAST model built
out of RazorWT terms. This is not really possible
because e.g.\ RazorAST requires us to add any two terms using
\verb$_+_$, but the addition that we have only works for terms of type
\verb$Nat$. Terms in our RazorAST algebra are either a pair of a
RazorWT type and a term of that type or a failure. We use
\verb$Maybe$ to express possible failure: \verb$just (A, t)$ and
\verb$nothing$ are both in the set \verb$Maybe (Σ I.Ty I.Tm)$, the
latter expresses failure. Failure propagates through the operations \verb$ite$, \verb$isZero$ and \verb$_+_$.
\begin{code}[hide]
import RazorAST
\end{code}
\begin{code}
Inf : RazorAST.Model
Inf = record
  { Tm      = Maybe (Σ I.Ty I.Tm)
  ; true    = just (I.Bool , I.true)
  ; false   = just (I.Bool , I.false)
  ; ite     = ite
  ; num     = λ n → just (I.Nat , I.num n)
  ; isZero  = isZero
  ; _+o_    = _+o_
  }
  where
    ite : Maybe (Σ I.Ty I.Tm) → Maybe (Σ I.Ty I.Tm) → Maybe (Σ I.Ty I.Tm) → Maybe (Σ I.Ty I.Tm)
    ite (just (I.Bool , t))  (just (I.Nat   , u))  (just (I.Nat   , v))  = just (I.Nat  , I.ite t u v)
    ite (just (I.Bool , t))  (just (I.Bool  , u))  (just (I.Bool  , v))  = just (I.Bool , I.ite t u v)
    ite _                    _                     _                     = nothing
          
    isZero : Maybe (Σ I.Ty I.Tm) → Maybe (Σ I.Ty I.Tm)
    isZero (just (I.Nat , t))  = just (I.Bool , I.isZero t)
    isZero _                   = nothing

    _+o_ : Maybe (Σ I.Ty I.Tm) → Maybe (Σ I.Ty I.Tm) → Maybe (Σ I.Ty I.Tm)
    just (I.Nat , t)  +o just (I.Nat , t')  = just (I.Nat , (t I.+o t'))
    _                 +o _                  = nothing
module Inf = RazorAST.Model Inf
\end{code}
Interpretation into this model gives us type inference.
\begin{code}
infer : RazorAST.I.Tm → Maybe (Σ I.Ty I.Tm)
infer = Inf.⟦_⟧
\end{code}

\begin{exe}[compulsory]
Here are some lists of lexical elements (written as strings). They are all accepted by the parser. Which ones are rejected by type inference? For the ones which are accepted, write down the RazorWT terms which are produced.
\begin{verbatim}
if true then true else num 0
if true then num 0 else num 0
if num 0 then num 0 else num 0
if num 0 then num 0 else true
true + zero
true + num 1
true + isZero false
true + isZero (num 0)
\end{verbatim}
\end{exe}

\begin{exe}[compulsory]
Here are some RazorAST terms. Which ones are rejected by type inference? For the ones which are accepted, write down the RazorWT terms which are produced.
\begin{verbatim}
ite true true (num 0)
ite true (num 0) (num 0)
ite (num 0) (num 0) (num 0)
true +o zero
true +o num 1
true +o isZero (num 1)
isZero (num 1) +o num 0
\end{verbatim}
\end{exe}

\subsection{Standard interpretation}

We define the standard model (set model, denotational
semantics). The idea is that all operators in our object language are
given by their metatheoretic counterparts.
\begin{code}

St : Model
St = record
  { Ty      = Set
  ; Tm      = λ T → T
  ; Nat     = ℕ
  ; Bool    = 𝟚
  ; true    = tt
  ; false   = ff
  ; ite     = if_then_else_
  ; num     = λ n → n
  ; isZero  = λ { zero → tt ; _ → ff }
  ; _+o_    = _+_
  }
module St = Model St
\end{code}
Using the iterator we get an interpreter (the metacircular interpreter, evaluator, normaliser) for our language:
\begin{code}
norm : ∀{A} → I.Tm A → St.⟦ A ⟧T
norm = St.⟦_⟧t
\end{code}

We were not able to define the standard interpreter for RazorAST
because there we had meaningless programs. For example, we would have
had to interpret both \verb$Bool$ and \verb$Nat$ by the same set
(c.f.\ Exercise \ref{ex:cstyle}).

\subsection{Typing relation}

The traditional way of defining the well-typed syntax is by defining a
binary relation between syntactic types and syntactic RazorAST
terms (see e.g.\ \cite{harper}). This relation is defined inductively as follows.
\begin{code}
module I' = RazorAST.I
data _⦂_  :  I'.Tm → I.Ty → Prop where
  true    :
                               -----------------------
                               I'.true ⦂ I.Bool
  false   :
                               -----------------------
                               I'.false ⦂ I.Bool
  ite     :  ∀{t u v A} →
                               t ⦂ I.Bool                →
                               u ⦂ A                     →
                               v ⦂ A                     →
                               -----------------------
                               I'.ite t u v ⦂ A
  num     :  ∀{n} →
                               -----------------------
                               I'.num n ⦂ I.Nat
  isZero  :  ∀{t} →
                               t ⦂ I.Nat                 →
                               -----------------------
                               I'.isZero t ⦂ I.Bool
  _+o_    :  ∀{u v} →
                               u ⦂ I.Nat                 →
                               v ⦂ I.Nat                 →
                               -----------------------
                               (u I'.+o v) ⦂ I.Nat
\end{code}
\begin{exe}
  Show that there is an isomorphism between \verb$I.Tm A$ and \verb$Σ I'.Tm (_⦂ A)$.
\end{exe}

We defined well-typed terms directly because we do not want to talk
about non-well-typed terms in the same way as we are not interested in
programs with non-matching brackets.
