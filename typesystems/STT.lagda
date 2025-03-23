\part{Type systems}

\chapter{Higher order function space}
\label{ch:STT}

\begin{tcolorbox}[title=Learning goals of this chapter]
  Rules for function space.
  Uniqueness rule.
  Currying.
  Relationship of metatheoretic and object theoretic function space.
  Normal forms when we have \verb$η$ rule.
  Bidirectional typechecking.
\end{tcolorbox}

We saw in Subsection \ref{sec:def-firstorder} that the language Def
already has first order function space, but this is not first class,
for example there is no type of first order functions.  Now we extend
Def with arbitrary higher order functions which are first class, e.g.\
they can be passed around as arguments to functions.
\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module STT where

open import Lib

record Model {i j} : Set (lsuc (i ⊔ j)) where
  infixl 6 _[_]
  infixl 5 _▹_
  infixl 7 _+o_
  infixr 6 _⇒_
  infixl 5 _$_

  field
    Ty        : Set i
    Con       : Set i
    Var       : Con → Ty → Set j
    Tm        : Con → Ty → Set j
    Sub       : Con → Con → Set j
    
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

    Bool      : Ty
    true      : ∀{Γ} → Tm Γ Bool
    false     : ∀{Γ} → Tm Γ Bool
    ite       : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
    iteβ₁     : ∀{Γ A u v} → ite {Γ}{A} true  u v ≡ u
    iteβ₂     : ∀{Γ A u v} → ite {Γ}{A} false u v ≡ v
    true[]    : ∀{Γ Δ σ} → true  {Γ} [ σ ] ≡ true  {Δ}
    false[]   : ∀{Γ Δ σ} → false {Γ} [ σ ] ≡ false {Δ}
    ite[]     : ∀{Γ Δ A t u v σ} → (ite {Γ}{A} t u v) [ σ ] ≡ ite {Δ} (t [ σ ]) (u [ σ ]) (v [ σ ])
    
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
    
  def : ∀{Γ A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
  def u t = t [ ⟨ u ⟩ ]
  field
\end{code}
An STT-model is a Def-model extended with the following components:
\begin{code}
    _⇒_    : Ty → Ty → Ty
    lam    : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
    _$_    : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    ⇒β     : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A} → lam t $ u ≡ t [ ⟨ u ⟩ ]
    ⇒η     : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → t ≡ lam (t [ p ] $ var vz)
    lam[]  : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{Δ}{σ : Sub Δ Γ} → lam t [ σ ] ≡ lam (t [ σ ⁺ ])
    $[]    : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{Δ}{σ : Sub Δ Γ} →
             (t $ u) [ σ ] ≡ (t [ σ ]) $ (u [ σ ])
\end{code}
In STT (simple type theory), there are three ways to form types: \verb$Bool$, \verb$Nat$,
and for any two types \verb$A$ and \verb$B$, we also have a type
\verb$A ⇒ B$. So types are binary trees with \verb$Nat$ or \verb$Bool$ at the leaves.
\begin{code}[hide]
open import STT.Syntax
\end{code}
\verb$lam$ is a binder, it binds a variable (of type \verb$A$) in its
first (and only) explicit argument.
The operator \verb$_⇒_$ is right-associative, e.g.\ \verb$A ⇒ B ⇒ C = A ⇒ (B ⇒ C)$.
To match this, \verb._$_. is left-associative, e.g.\ \verb.t $ u $ v = (t $ u) $ v.

We group the operators and equations for \verb$_⇒_$:
\begin{itemize}
\item type introduction: \verb$_⇒_$,
\item constructor (called abstraction): \verb$lam$,
\item destructor (called application): \verb._$_.,
\item computation: \verb$⇒β$,
\item uniqueness: \verb$⇒η$,
\end{itemize}
A concise way to state the rules for function space is the following
natural isomorphism, the right to left direction can be defined using \verb._$_..
\begin{verbatim}
lam : Tm (Γ ▹ A) B ≅ Tm Γ (A ⇒ B) : app
\end{verbatim}

An example function with an example on how it computes:
\begin{code}
add2 : Tm ◇ (Nat ⇒ Nat)
add2 = lam (v0 +o num 2)

add2$3 : add2 $ num 3 ≡ num 5
add2$3 =
  add2 $ num 3
                                                 ≡⟨ refl ⟩
  lam (v0 +o num 2) $ num 3                          
                                                 ≡⟨ ⇒β ⟩
  (v0 +o num 2) [ ⟨ num 3 ⟩ ]                          
                                                 ≡⟨ +[] ⟩
  (v0  [ ⟨ num 3 ⟩ ]) +o (num 2 [ ⟨ num 3 ⟩ ])                          
                                                 ≡⟨ cong (_+o (num 2 [ ⟨ num 3 ⟩ ])) vz[⟨⟩] ⟩
  num 3 +o (num 2 [ ⟨ num 3 ⟩ ])                          
                                                 ≡⟨ cong (num 3 +o_) num[] ⟩
  num 3 +o num 2                          
                                                 ≡⟨ +β ⟩
  num 5
                                                 ∎
\end{code}
\begin{exe}[compulsory]
Derive the typing of
\textnormal{\begin{code}
apply2x : Tm ◇ ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat)
apply2x = lam (lam (v1 $ (v1 $ v0)))
\end{code}}
\end{exe}
\begin{exe}[compulsory]
What is the type of the following terms?
\begin{verbatim}
lam (isZero (ite v0 (num 1) (num 0)))
lam (lam (ite v0 (isZero v1) false))
lam (lam (v1 +o (v0 $ v1)))
lam (lam (num 1 +o (v1 $ v0)))
\end{verbatim}
\end{exe}
\begin{exe}[compulsory]
Prove
\textnormal{
\begin{code}
apply2x-example : apply2x $ add2 $ num 3 ≡ num 7
\end{code}
\begin{code}[hide]
apply2x-example = exercisep
\end{code}}
\end{exe}
Representing two-parameter functions as iterated function space as in the following exercise is named after Haskell Curry and is called \emph{currying}.
\begin{exe}[compulsory]
Define the following functions on booleans.
\textnormal{
\begin{code}
and  : Tm ◇ (Bool ⇒ Bool ⇒ Bool)
or   : Tm ◇ (Bool ⇒ Bool ⇒ Bool)
neg  : Tm ◇ (Bool ⇒ Bool)
\end{code}
\begin{code}[hide]
and = exercise
or  = exercise
neg = exercise
\end{code}}
\end{exe}
\begin{exe}[compulsory]
Define the identity function and function composition, and show the following equations relating them.
\textnormal{
\begin{code}
id    : ∀{Γ A} → Tm Γ (A ⇒ A)
comp  : ∀{Γ A B C} → Tm Γ ((B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
idl   : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → comp $ id $ t ≡ t
idr   : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → comp $ t $ id ≡ t
ass   : ∀{Γ A B C D}{t : Tm Γ (A ⇒ B)}{t' : Tm Γ (B ⇒ C)}{t'' : Tm Γ (C ⇒ D)} →
        comp $ (comp $ t'' $ t') $ t ≡ comp $ t'' $ (comp $ t' $ t)
\end{code}
\begin{code}[hide]
id   = exercise
comp = exercise
idl  = exercisep
idr  = exercisep
ass  = exercisep
\end{code}}
\end{exe}
\begin{exe}[recommended]
Define Moses Schönfinkel's \verb$K$ and \verb$S$ combinators and show their computation rules
(see also Section \ref{sec:SK}).
\textnormal{
\begin{code}
K   : ∀{Γ A B} → Tm Γ (A ⇒ B ⇒ A)
S   : ∀{Γ A B C} → Tm Γ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
Kβ  : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → K $ u $ v ≡ u
Sβ  : ∀{Γ A B C}{t : Tm Γ (A ⇒ B ⇒ C)}{u : Tm Γ (A ⇒ B)}{v : Tm Γ A} →
      S $ t $ u $ v ≡ t $ v $ (u $ v) 
\end{code}
\begin{code}[hide]
K  = exercise
S  = exercise
Kβ = exercisep
Sβ = exercisep
\end{code}}
\end{exe}
\begin{exe}[recommended]
Derive the ``categorical application operator'' \verb$ap$, show that it is the inverse of \verb$lam$. Also show
its substitution rule \verb$app[]$.
\textnormal{
\begin{code}
app    : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm (Γ ▹ A) B
appβ   : ∀{Γ A B}{t : Tm (Γ ▹ A) B} → app (lam t) ≡ t
appη   : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → lam (app t) ≡ t
app[]  : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{Δ}{σ : Sub Δ Γ} → app t [ σ ⁺ ] ≡ app (t [ σ ])
\end{code}
\begin{code}[hide]
app   = exercise
appβ  = exercisep
appη  = exercisep
app[] = exercisep
\end{code}}
\end{exe}
\begin{exe}[compulsory]
How many different elements does \verb$Tm ◇ (Bool ⇒ Bool)$ have? Define them! (See also normalisation below.)
\end{exe}
\begin{exe}[compulsory]
Compare the sets \verb$Tm ◇ (Bool ⇒ Bool)$ and \verb$Tm ◇ Bool → Tm ◇ Bool$. Is there a logical equivalence between them?
\end{exe}
\begin{exe}[compulsory]
Internalise \verb$isZero$, that is, define \verb$isZero'$ as below. Similarly, internalise the functions \verb$_+o_$ and \verb$ite$.
\textnormal{
\begin{code}
isZero'  : ∀{Γ} → Tm Γ (Nat ⇒ Bool)
add'     : ∀{Γ} → Tm Γ (Nat ⇒ Nat ⇒ Nat)
ite'     : ∀{Γ A} → Tm Γ (Bool ⇒ A ⇒ A ⇒ A)
\end{code}
\begin{code}[hide]
isZero' = exercise
add'    = exercise
ite'    = exercise
\end{code}}
\end{exe}
\begin{exe}[very hard]
Show that for any model, \verb$Tm Γ (A ⇒ B)$ is isomorphic to \\
\verb$Σ (∀{Δ}(γ : PSub Δ Γ) → Tm Δ A → Tm Δ B) λ f → ∀{γ a δ} → f γ a [ δ ]P ≡ f (γ ∘ δ) (a [ δ ]P)$,
where \verb$PSub$ is a sort of parallel substitutions which have composition. A \verb$PSub Δ (◇ ▹ A₁ ▹ ... Aₙ)$
is a list of \verb$n$ terms all in context \verb$Δ$ of types \verb$A₁$, \dots, \verb$Aₙ$, respectively.
\verb$_[_]P$ is instantiation of terms with parallel substitutions, this can be defined by iterating \verb$_[_]$.
\end{exe}

\section{Standard model}

\begin{code}[hide]
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
\end{code}
\begin{code}
  ; _⇒_       = λ A B → A → B
  ; lam       = λ t γ → λ a → t (γ , a)
  ; _$_       = λ t u γ → t γ (u γ)
  ; ⇒β        = refl
  ; ⇒η        = refl
  ; lam[]     = refl
  ; $[]       = refl
\end{code}
\begin{code}[hide]
  }
\end{code}

\section{Normalisation}

Normal forms are like in Def, but there is a twist.
\begin{code}
infixl 5 _$Ne_

data Ne : Con → Ty → Set
data Nf : Con → Ty → Set
data Ne where
  varNe     : ∀{Γ A} → Var Γ A → Ne Γ A
  iteNe     : ∀{Γ A} → Ne Γ Bool → Nf Γ A → Nf Γ A → Ne Γ A
  isZeroNe  : ∀{Γ} → Ne Γ Nat → Ne Γ Bool
  _+NeNe_   : ∀{Γ} → Ne Γ Nat → Ne Γ Nat → Ne Γ Nat
  _+NeNf_   : ∀{Γ} → Ne Γ Nat → ℕ → Ne Γ Nat
  _+NfNe_   : ∀{Γ} → ℕ → Ne Γ Nat → Ne Γ Nat
  _$Ne_     : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

data Nf where
  neuBool   : ∀{Γ} → Ne Γ Bool → Nf Γ Bool
  neuNat    : ∀{Γ} → Ne Γ Nat → Nf Γ Nat
  trueNf    : ∀{Γ} → Nf Γ Bool
  falseNf   : ∀{Γ} → Nf Γ Bool
  numNf     : ∀{Γ} → ℕ → Nf Γ Nat
  lamNf     : ∀{Γ A B} → Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)

⌜_⌝Ne : ∀{Γ A} → Ne Γ A → Tm Γ A
⌜_⌝Nf : ∀{Γ A} → Nf Γ A → Tm Γ A
\end{code}
\begin{code}[hide]
⌜ varNe x       ⌝Ne = var x
⌜ iteNe n v v'  ⌝Ne = ite ⌜ n ⌝Ne ⌜ v ⌝Nf ⌜ v' ⌝Nf
⌜ isZeroNe n    ⌝Ne = isZero ⌜ n ⌝Ne
⌜ n +NeNe n'    ⌝Ne = ⌜ n ⌝Ne +o ⌜ n ⌝Ne
⌜ n +NeNf i     ⌝Ne = ⌜ n ⌝Ne +o num i
⌜ i +NfNe n     ⌝Ne = num i +o ⌜ n ⌝Ne
⌜ n $Ne v       ⌝Ne = ⌜ n ⌝Ne $ ⌜ v ⌝Nf
⌜ neuBool n     ⌝Nf = ⌜ n ⌝Ne
⌜ neuNat  n     ⌝Nf = ⌜ n ⌝Ne
⌜ trueNf        ⌝Nf = true
⌜ falseNf       ⌝Nf = false
⌜ numNf i       ⌝Nf = num i
⌜ lamNf v       ⌝Nf = lam ⌜ v ⌝Nf
\end{code}
Only neutral terms of base types (\verb$Bool$ and \verb$Nat$) are included in normal
forms (this was also true in Def because there were no other types). Without this
restriction, we would have two different normal forms for a variabe of a function type:
\verb$q$ which is equal to \verb.lam (q [ p ]) $ q.. We have to do this whenever we have
uniqueness rules.

\begin{exe}
What are the normal form of the following terms?
\textnormal{
\begin{code}
t1 : Σsp (Nf (◇ ▹ Nat ⇒ Bool) (Nat ⇒ Bool)) λ v → ⌜ v ⌝Nf ≡ v0
t2 : Σsp (Nf (◇ ▹ Bool) Bool) λ v → ⌜ v ⌝Nf ≡ v0
t3 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ v0
t4 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ num 1 +o v0
t5 : Σsp (Nf ◇ Nat) λ v → ⌜ v ⌝Nf ≡ num 1 +o num 2
t6 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ isZero (v0 +o num 1)
t7 : Σsp (Nf ◇ Bool) λ v → ⌜ v ⌝Nf ≡ isZero (num 2)
t8 : Σsp (Nf ◇ Bool) λ v → ⌜ v ⌝Nf ≡ lam (isZero v0) $ num 0
t9 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ lam (isZero v0) $ v0
t10 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ lam (isZero v0) $ (v0 +o num 1)
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
t9 = exercise
t10 = exercise
\end{code}}
\end{exe}

Recursive normalisation as for Def does not work as for STT. This is because when
defining normal application we need instantiation and when defining instantiation, we need
normal application and it is not obvious that such mutual definition terminates.
\footnote{It does terminate and normalisation can be defined this way, this is called
hereditary substitution \cite{DBLP:conf/icfp/KellerA10}.}
\begin{verbatim}
_$Nf_  : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B
_[_]Ne : Ne Γ A → Sub Δ Γ → Nf Δ A
lamNf t $Nf u = t [ ⟨ u ⟩ ]Nf
(t $Ne a) [ γ ]Ne = t [ γ ]Ne $Nf a [ γ ]Ne
\end{verbatim}

However we can use the method of logical predicates (like in Section \ref{sec:SK}). Instead of proving
normalisation by induction on terms, we do induction on types as well. For each type, we define a predicate on terms of that type.
For contexts we define a predicate on lists of terms with types in that context by iterating the predicate for the types.
For terms \verb$Tm Γ A$, we show by induction that they respect the predicate: if the predicate holds for a list of terms with types in \verb$Γ$, then
the predicate at \verb$A$ holds for the term substituted by the list of terms. Similarly, substitutions respect the predicate.
Then we show by induction on types that if the predicate holds for a term, then it is in normal form.

TODO: show full normalisation.

TODO: bidirectional type checking
