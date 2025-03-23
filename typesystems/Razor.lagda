\section{Well-typed syntax with equations}\label{sec:Razor}

In the well-typed syntax, we still had too many terms in a sense: for
example, the terms \verb$I.true$ and
\verb$I.isZero (I.num 0)$ were different, even if they
should be equal in a sensible semantics. The information which terms
should be the same (usually this is called operational semantics) was
missing. Now we add this information in the form of equalities.

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}

module Razor where

open import Lib
module I where
  infixl 7 _+o_
  
  data Ty     : Set where
    Nat       : Ty
    Bool      : Ty
  
  postulate
    Tm        : Ty → Set
    true      : Tm Bool
    false     : Tm Bool
    ite       : ∀{A} → Tm Bool → Tm A → Tm A → Tm A
    num       : ℕ → Tm Nat
    isZero    : Tm Nat → Tm Bool
    _+o_      : Tm Nat → Tm Nat → Tm Nat
    iteβ₁     : ∀{A}{u v : Tm A} → ite true u v ≡ u
    iteβ₂     : ∀{A}{u v : Tm A} → ite false u v ≡ v
    isZeroβ₁  : isZero (num 0) ≡ true
    isZeroβ₂  : {n : ℕ} → isZero (num (1 + n)) ≡ false
    +β        : {m n : ℕ} → num m +o num n ≡ num (m + n)
\end{code}

A Razor model (without any qualifiers) consists of the following
components. The only difference from RazorWT is the addition of the
five equations.
\begin{code}
record Model {ℓ ℓ'} : Set (lsuc (ℓ ⊔ ℓ')) where
  field
    Ty        : Set ℓ
    Tm        : Ty → Set ℓ'
    Nat       : Ty
    Bool      : Ty
    true      : Tm Bool
    false     : Tm Bool
    ite       : {A : Ty} → Tm Bool → Tm A → Tm A → Tm A
    num       : ℕ → Tm Nat
    isZero    : Tm Nat → Tm Bool
    _+o_      : Tm Nat → Tm Nat → Tm Nat
    iteβ₁     : ∀{A}{u v : Tm A} → ite true u v ≡ u
    iteβ₂     : ∀{A}{u v : Tm A} → ite false u v ≡ v
    isZeroβ₁  : isZero (num 0) ≡ true
    isZeroβ₂  : {n : ℕ} → isZero (num (1 + n)) ≡ false
    +β        : {m n : ℕ} → num m +o num n ≡ num (m + n)
\end{code}
The iterator is given as before.
\begin{code}
  ⟦_⟧T         : I.Ty → Ty
  ⟦ I.Nat ⟧T   = Nat
  ⟦ I.Bool ⟧T  = Bool

  postulate
    ⟦_⟧t       : {A : I.Ty} → I.Tm A → Tm ⟦ A ⟧T
    ⟦true⟧     :            ⟦ I.true      ⟧t ≈ true
    ⟦false⟧    :            ⟦ I.false     ⟧t ≈ false
    ⟦ite⟧      : {A : I.Ty}{t : I.Tm I.Bool}{u v : I.Tm A} →
                            ⟦ I.ite t u v ⟧t ≈ ite ⟦ t ⟧t ⟦ u ⟧t ⟦ v ⟧t
    ⟦num⟧      : {n : ℕ}  → ⟦ I.num n     ⟧t ≈ num n
    ⟦isZero⟧   : ∀{t}     → ⟦ I.isZero t  ⟧t ≈ isZero ⟦ t ⟧t
    ⟦+o⟧       : ∀{u v}   → ⟦ u I.+o v    ⟧t ≈ ⟦ u ⟧t +o ⟦ v ⟧t
\end{code}
\begin{code}[hide]
    {-# REWRITE ⟦true⟧ ⟦false⟧ ⟦ite⟧ ⟦num⟧ ⟦isZero⟧ ⟦+o⟧ #-}

I : Model
I = record { Ty = I.Ty ; Tm = I.Tm ; Nat = I.Nat ; Bool = I.Bool ; true = I.true ; false = I.false; ite = I.ite ; num = I.num ; isZero = I.isZero ; _+o_ = I._+o_ ; iteβ₁ = I.iteβ₁ ; iteβ₂ = I.iteβ₂ ; isZeroβ₁ = I.isZeroβ₁ ; isZeroβ₂ = I.isZeroβ₂ ; +β = I.+β }
\end{code}
We also have dependent models and an eliminator.
\begin{code}[hide]
record DepModel {ℓ ℓ'} : Set (lsuc (ℓ ⊔ ℓ')) where
  field
    Ty∙        : I.Ty → Set ℓ
    Tm∙        : {A : I.Ty} → Ty∙ A → I.Tm A → Set ℓ'
    Nat∙       : Ty∙ I.Nat
    Bool∙      : Ty∙ I.Bool
    true∙      : Tm∙ Bool∙ I.true
    false∙     : Tm∙ Bool∙ I.false
    ite∙       : {A : I.Ty}{A∙ : Ty∙ A} → ∀{t u v} →
                 Tm∙ Bool∙ t → Tm∙ A∙ u → Tm∙ A∙ v → Tm∙ A∙ (I.ite t u v)
    num∙       : (n : ℕ) → Tm∙ Nat∙ (I.num n)
    isZero∙    : ∀{t} → Tm∙ Nat∙ t → Tm∙ Bool∙ (I.isZero t)
    _+o∙_      : ∀{u v} → Tm∙ Nat∙ u → Tm∙ Nat∙ v → Tm∙ Nat∙ (u I.+o v)
    iteβ₁∙     : {A : I.Ty}{u v : I.Tm A}{A∙ : Ty∙ A}{u∙ : Tm∙ A∙ u}{v∙ : Tm∙ A∙ v} →
                 ((Tm∙ A∙) ~) I.iteβ₁ (ite∙ true∙ u∙ v∙) u∙
    iteβ₂∙     : {A : I.Ty}{u v : I.Tm A}{A∙ : Ty∙ A}{u∙ : Tm∙ A∙ u}{v∙ : Tm∙ A∙ v} →
                 ((Tm∙ A∙) ~) I.iteβ₂ (ite∙ false∙ u∙ v∙) v∙
    isZeroβ₁∙  : ((Tm∙ Bool∙) ~) I.isZeroβ₁ (isZero∙ (num∙ 0)) true∙
    isZeroβ₂∙  : {n : ℕ} → ((Tm∙ Bool∙) ~) I.isZeroβ₂ (isZero∙ (num∙ (1 + n))) false∙
    +β∙        : {m n : ℕ} → ((Tm∙ Nat∙) ~) I.+β (num∙ m +o∙ num∙ n) (num∙ (m + n))
                
  ⟦_⟧T : (A : I.Ty) → Ty∙ A
  ⟦ I.Nat ⟧T = Nat∙
  ⟦ I.Bool ⟧T = Bool∙
  postulate
    ⟦_⟧t       : {A : I.Ty}(t : I.Tm A) → Tm∙ ⟦ A ⟧T t
    ⟦true⟧     :            ⟦ I.true      ⟧t ≈ true∙
    ⟦false⟧    :            ⟦ I.false     ⟧t ≈ false∙
    ⟦ite⟧      : {A : I.Ty}{t : I.Tm I.Bool}{u v : I.Tm A} →
                            ⟦ I.ite t u v ⟧t ≈ ite∙ ⟦ t ⟧t ⟦ u ⟧t ⟦ v ⟧t
    ⟦num⟧      : {n : ℕ}  → ⟦ I.num n     ⟧t ≈ num∙ n
    ⟦isZero⟧   : ∀{t}     → ⟦ I.isZero t  ⟧t ≈ isZero∙ ⟦ t ⟧t
    ⟦+o⟧       : ∀{u v}   → ⟦ u I.+o v    ⟧t ≈ ⟦ u ⟧t +o∙ ⟦ v ⟧t
    {-# REWRITE ⟦true⟧ ⟦false⟧ ⟦ite⟧ ⟦num⟧ ⟦isZero⟧ ⟦+o⟧ #-}
\end{code}

Now we can reproduce the evaluation of the example program from the
beginning of Chapter \ref{ch:precision} as an equality between terms.
\begin{code}[hide]
module example where
  open I

  ex : ite (isZero (num 0 +o num 1)) false (isZero (num 0)) ≡ true
  ex =
\end{code}
\begin{code}
    ite (isZero (num 0 +o num 1))  false (isZero (num 0))
      ≡⟨ cong (λ x → ite (isZero x) false (isZero (num 0))) +β ⟩
    ite (isZero (num 1))           false (isZero (num 0))
      ≡⟨ cong (λ x → ite x false (isZero (num 0))) isZeroβ₂ ⟩
    ite false                      false (isZero (num 0))
      ≡⟨ iteβ₂ ⟩
    isZero (num 0)
      ≡⟨ isZeroβ₁ ⟩
    true
      ∎
\end{code}
Two terms which result in the same boolean or number are equal.

The type inference algorithm given for RazorWT also works for
Razor. We can't calculate the height of a term anymore as before
because of the equalities. Every function has to preserve the
equalities. For example, we need that \verb$height (isZero (num 0)) = height true$.
If we view these terms as syntax trees, their height is 1 and 0, respectively.

\subsection{Standard model and equational consistency}
\label{sec:razor-standard}

The term \verb$ite (isZero (num 0 +o num 1)) false (isZero (num 0))$
was built using the operators of our language. Every model supports
these operations, hence the term can be built in any model. The
equality \verb$ite (isZero (num 0 +o num 1)) false (isZero (num 0)) = true$
was built using the equations in our language which hold in
every model. Hence the equality also holds in every model. Such a term
or equation is called \emph{derivable}. A derivable term can be
constructed in any model, a derivable equation holds in every
model. In contrast, there are properties that we can only prove using
induction: these hold in the syntax, but might not hold for every
model. For example, the fact that for any \verb$t : Tm Bool$ we have
\verb$t = true$ or \verb$t = false$ holds in the syntax (this is a
consequence of normalisation, see below) but not in an arbitrary
model. Such properties are called \emph{admissible}.

Another property of the syntax is that \verb$true ≠ false$. We can show this using the standard model.

The operators in the standard model are defined exactly as for RazorWT, but we also have to
prove the five equalities \verb$iteβ₁$, \dots, \verb$+β$: they all hold by definition.
\begin{code}
St : Model
St = record
  { Ty        = Set
  ; Tm        = λ A → A
  ; Nat       = ℕ
  ; Bool      = 𝟚
  ; true      = tt
  ; false     = ff
  ; ite       = if_then_else_
  ; num       = λ n → n
  ; isZero    = iteℕ tt (λ _ → ff)
  ; _+o_      = _+_
  ; iteβ₁     = refl
  ; iteβ₂     = refl
  ; isZeroβ₁  = refl
  ; isZeroβ₂  = refl
  ; +β        = refl
  }
module St = Model St
\end{code}
From the standard model we obtain \emph{equational consistency} of our
language, that is, there are terms which are not equal. This means
that we didn't add too many equalities when defining the language.
In the syntax, if \verb$true$ was equal to \verb$false$, then their standard
interpretations would also be equal, but then \verb$tt$ would be equal
to \verb$ff$.
\begin{code}[hide]
module EquationalConsistency where
\end{code}
\begin{code}
  true≠false : ¬ (I.true ≡ I.false)
  true≠false e = tt≠ff (cong St.⟦_⟧t e)
\end{code}

If we are not careful when defining the equations of the language, it is easy to lose equational consistency, and then our language becomes useless, as any two terms will be equal.

As for any language, we can define a trivial model.
\begin{code}
Triv : Model
Triv = record
  { Ty        = Lift ⊤
  ; Tm        = λ _ → Lift ⊤
  ; Nat       = mk triv
  ; Bool      = mk triv
  ; true      = mk triv
  ; false     = _
  ; ite       = _
  ; num       = _
  ; isZero    = _
  ; _+o_      = _
  ; isZeroβ₁  = refl
  ; isZeroβ₂  = refl
  ; +β        = refl
  ; iteβ₁     = refl
  ; iteβ₂     = refl
  }
module Triv = Model Triv
\end{code}
In the trivial model, any two terms are equal, hence all the equalities that can be described in the language, hold. For example, in this model we not only have
\verb$true = false$, but also \verb$Nat = Bool$ and \verb$true = num 5$ (this equality only makes sense because we know that \verb$Nat = Bool$). We also have that for any \verb$t : Tm Bool$, \verb$t = true$ or \verb$t = false$, trivially.

\begin{exe}[recommended]
  Construct a model in which it does not hold that for a \verb$t : Tm Bool$ we have \verb$t = true$ or \verb$t = false$.
\end{exe}

\begin{exe}[compulsory]
Show that if \verb$true$ = \verb$false$ in a model, then any two
\verb$u, v : Tm Nat$ are equal in that model. A consequence is that if
a compiler compiles true and false to the same code, then it compiles
all natural numbers to the same code.
\end{exe}

\subsection{Normalisation}
\label{sec:razor-norm}

Normalisation essentially says that the language can also be defined without equations. That is, there is a subset of syntactic terms called \emph{normal forms} which are pairwise distinct and every syntactic term is equal to a normal form. Syntactic terms are quotiented by the equations of the language and normalisation implies that there is a function which selects a representative from each equivalence class. For Razor, there are two normal forms of type \verb$Bool$ (\verb$true$ and \verb$false$) and countably many normal forms of type \verb$Nat$ (\verb$num n$ for each \verb$n : ℕ$). Thus we simply define normal forms of type \verb$A$ by interpreting the \verb$A$ in the standard model, together with an injection \verb$⌜_⌝$ (called quotation) into syntactic terms.
\begin{code}
Nf : I.Ty → Set
Nf A = St.⟦ A ⟧T

⌜_⌝ : ∀ {A} → St.⟦ A ⟧T → I.Tm A
⌜_⌝ {I.Bool} tt = I.true
⌜_⌝ {I.Bool} ff = I.false
⌜_⌝ {I.Nat} = I.num
\end{code}
The normalisation function is simply interpretation into the standard model:
\begin{code}
norm : {A : I.Ty} → I.Tm A → Nf A
norm = St.⟦_⟧t 
\end{code}
\emph{Completeness of normalisation} says that every term is equal to
its normal form (followed by quote). In our case, this means that every
boolean term (element of \verb$I.Tm I.Bool$) is either true or false
and every natural number term is a finite application of \verb$I.suc$s
on \verb$I.zero$. We first show that quote commutes with
the operations \verb$ite$, \verb$isZero$ and \verb$_+_$.
\begin{code}
⌜ite⌝ : ∀{b A}{u v : St.⟦ A ⟧T} → ⌜ if b then u else v ⌝ ≡ I.ite {A} ⌜ b ⌝ ⌜ u ⌝ ⌜ v ⌝
⌜ite⌝ {tt}{A} = I.iteβ₁ ⁻¹
⌜ite⌝ {ff}{A} = I.iteβ₂ ⁻¹

⌜isZero⌝ : ∀{n} → ⌜ iteℕ tt (λ _ → ff) n ⌝ ≡ I.isZero ⌜ n ⌝
⌜isZero⌝ {zero}   = I.isZeroβ₁ ⁻¹
⌜isZero⌝ {suc n}  = I.isZeroβ₂ ⁻¹

⌜+⌝ : ∀{m n} → ⌜ m + n ⌝ ≡ ⌜ m ⌝ I.+o ⌜ n ⌝
⌜+⌝ {m}{n} = I.+β ⁻¹
\end{code}
Now we can prove completeness of normalisation by induction on terms.
\begin{code}
Comp : DepModel
Comp = record
  { Ty∙        = λ _ → Lift ⊤
  ; Tm∙        = λ _ t → Lift (⌜ St.⟦ t ⟧t ⌝ ≡ t)
  ; Nat∙       = _
  ; Bool∙      = _
  ; num∙       = λ n → mk refl
  ; isZero∙    = λ {t} t∙ → mk (⌜isZero⌝ ◾ cong I.isZero (un t∙))
  ; _+o∙_      = λ {u}{v} u∙ v∙ → mk (
                (⌜+⌝ {St.⟦ u ⟧t}{St.⟦ v ⟧t}) ◾
                (cong₂ I._+o_ (un u∙) (un v∙)))
  ; true∙      = mk refl
  ; false∙     = mk refl
  ; ite∙       = λ {A}{A∙}{t}{u}{v} t∙ u∙ v∙ → mk (
                (⌜ite⌝ {St.⟦ t ⟧t}{A}{St.⟦ u ⟧t}{St.⟦ v ⟧t}) ◾
                (cong₃ I.ite (un t∙) (un u∙) (un v∙)))
  ; iteβ₁∙      = refl
  ; iteβ₂∙     = refl
  ; isZeroβ₁∙  = refl
  ; isZeroβ₂∙  = refl
  ; +β∙        = refl
  }
module Comp = DepModel Comp

comp : {A : I.Ty}{t : I.Tm A} → ⌜ norm {A} t ⌝ ≡ t
comp {t = t} = un Comp.⟦ t ⟧t
\end{code}

\emph{Stability of normalisation} says that there is no junk in normal
forms, for every normal form there is a term which normalises to it.
\begin{code}
stab : {A : I.Ty}{t : St.⟦ A ⟧T} → norm {A} ⌜ t ⌝ ≡ t
stab {I.Nat}  {t}  = refl
stab {I.Bool} {tt} = refl
stab {I.Bool} {ff} = refl
\end{code}

We used all the equations of Razor in the completeness proof. If we
take out e.g.\ the rule \verb$isZeroβ₂$ from the definition of the
language, we cannot prove completeness anymore because we have
elements of \verb$I.Tm I.Bool$ which are neither \verb$I.true$, nor
\verb$I.false$. The following (Razor without \verb$isZeroβ₂$) model distinguishes \verb$true$,
\verb$false$ and \verb$isZero (num 1)$.
\begin{code}
module RazorIncomplete where
  Ty        : Set₁
  Tm        : Ty → Set
  Nat       : Ty
  Bool      : Ty
  num       : ℕ → Tm Nat
  isZero    : Tm Nat → Tm Bool
  _+o_      : Tm Nat → Tm Nat → Tm Nat
  true      : Tm Bool
  false     : Tm Bool
  ite       : ∀{A} → Tm Bool → Tm A → Tm A → Tm A
  isZeroβ₁  : isZero (num 0)     ≡ true
  +β        : ∀{m n} → num m +o num n ≡ num (m + n)
  iteβ₁     : ∀{A}{u v : Tm A} → ite true   u v ≡ u
  iteβ₂     : ∀{A}{u v : Tm A} → ite false  u v ≡ v

  Ty                 = Set
  Tm A               = A
  Nat                = ℕ
  Bool               = Maybe 𝟚
  num                = λ n → n
  isZero zero        = just tt
  isZero (suc _)     = nothing
  _+o_               = _+_
  true               = just tt
  false              = just ff
  ite nothing u v    = u
  ite (just tt) u v  = u
  ite (just ff) u v  = v
  isZeroβ₁           = refl
  +β {m}{n}          = refl
  iteβ₁ {A}{u}{v}    = refl
  iteβ₂ {A}{u}{v}    = refl
  
  true≠false     : ¬ (true   ≡ false)
  true≠isZero1   : ¬ (true   ≡ isZero (num 1))
  false≠isZero1  : ¬ (false  ≡ isZero (num 1))
\end{code}
\begin{code}[hide]
  true≠false ()
  true≠isZero1 ()
  false≠isZero1 ()
\end{code}

\begin{exe}
  Define normalisation and prove its completeness using a modified standard model where \verb$Bool = Maybe 𝟚$. Show that stability does not hold.
\end{exe}

\begin{exe}[compulsory]
Show that \verb$I.true ≠ I.false$, but there are \verb$t$, \verb$u$, \verb$v$ such that \verb$I.true = I.ite t u v$. Why doesn't the RazorAST-method for proving disjointness of syntactic operators work?
\end{exe}

\begin{exe}[compulsory]
Show that \verb$I.num$ is injective, but \verb$I.isZero$ is not injective. Why doesn't the RazorAST-method for proving injectivity of syntactic operators work?
\end{exe}

\begin{exe}[compulsory]
  Show that in the syntax we have \verb$ite t u u = u$ for any \verb$t$, \verb$u$, and construct a model in which this doesn't hold.
\end{exe}

\begin{code}[hide]
module thisExe where
  A : Model
  A = record
    { Ty = Set
    ; Tm = λ A → Maybe A
    ; Nat = ℕ
    ; Bool = 𝟚
    ; true = just tt
    ; false = just ff
    ; ite = λ { (just tt) u v → u ; (just ff) u v → v ; _ _ _ → nothing }
    ; num = λ n → just n
    ; isZero = λ { (just zero) → just tt ; (just _) → just ff ; nothing → nothing }
    ; _+o_ = λ { (just m) (just n) → just (m + n) ; _ _ → nothing }
    ; iteβ₁ = λ {_}{u}{v} → refl
    ; iteβ₂ = λ {_}{u}{v} → refl
    ; isZeroβ₁ = refl
    ; isZeroβ₂ = refl
    ; +β = λ {m}{n} → refl
    }
  open Model A
  t : Tm Bool
  t = nothing
  u : Tm Nat
  u = just 3
  itetuu≠u : ¬ (ite t u u ≡ u)
  itetuu≠u ()
\end{code}

\begin{exe}[recommended]
Define a height function on terms which returns the height of the normal form of the term.
\end{exe}

\begin{exe}[recommended]
A model of a monoid over \verb$A$ has the following components.
\begin{alignat*}{10}
& \texttt{C} && \texttt{: Set} \\
& \texttt{f} && \texttt{: A → C} \\
& \texttt{\_∘\_}\, && \texttt{: C → C → C} \\
& \texttt{id} && \texttt{: C} \\
& \texttt{ass} && \texttt{: (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)} \\
& \texttt{idl} && \texttt{: id ∘ a ≡ a} \\
& \texttt{idr} && \texttt{: a ∘ id ≡ a}
\end{alignat*}
The initial model is called the free monoid over \verb$A$.

  Define normalisation and prove its completeness and stability for the free monoid over a set \verb$A$. Normal forms are simply lists of \verb$A$.
\end{exe}


\subsection{Transition relation}

The traditional way of defining equality of syntactic terms is using
transition relations on syntactic RazorAST terms (see e.g.\ \cite{harper}).
\begin{code}
module SmallStep where
  import RazorAST
  module I' = RazorAST.I
  data _↦_ : I'.Tm → I'.Tm → Prop where
    isZeroβ₁     :           I'.isZero (I'.num 0) ↦ I'.true
    isZeroβ₂     : ∀{n}   →  I'.isZero (I'.num (1 + n)) ↦ I'.false
    +β           : ∀{m n} → (I'.num m I'.+o I'.num n) ↦ I'.num (m + n)
    iteβ₁        : ∀{u v} →  I'.ite I'.true   u v ↦ u
    iteβ₂        : ∀{u v} →  I'.ite I'.false  u v ↦ v
  
    isZero-cong  : ∀{t t'}      → t  ↦ t'  → I'.isZero t     ↦ I'.isZero t'
    +-cong₁      : ∀{u v u'}    → u  ↦ u'  → (u I'.+o v)     ↦ (u' I'.+o v)
    +-cong₂      : ∀{u v v'}    → v  ↦ v'  → (u I'.+o v)     ↦ (u  I'.+o v')
    ite-cong     : ∀{t t' u v}  → t  ↦ t'  → (I'.ite t u v)  ↦ (I'.ite t' u v)
\end{code}
The idea is that if there is a \verb$p : t ↦ t'$, this means that the program
\verb$t$ evaluates to \verb$t'$ in one step. Running a program means that we have a
sequence of evaluation steps: \verb$t ↦ t' ↦ t'' ↦ ⋯$ 

There is a rewriting rule corresponding to each equation in the notion
of Razor-model. Then there are congruence rules (order rules) which
express which parameters and when should be evaluated. In our example
rewriting system above rewriting can happen anywhere except for
\verb$I'.ite$ it only happens in the first parameter.

Taking the reflexive transitive closure of \verb$↦$ we obtain the
multi-step rewriting relation \verb$↦*$, taking the symmetric closure
of \verb$↦*$ we get the conversion relation (definitional equality)
\verb$∼$ which in the case of Razor, corresponds to equality of
syntactic terms.
\begin{exe}
  Prove that \verb$t ≡ t'$ is logically equivalent to \verb$t ~ t'$ for all \verb$t$ and \verb$t'$.
\end{exe}

For other languages, this is not necessarily the case. In general, the
transition system contains more information than the description with
equations. Transition is directed and is not necessarily a
congruence. In these course notes we only present languages where
there is no such additional information.
