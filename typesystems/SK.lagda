\section{Making bindings first order via combinators}
\label{sec:SK}

In this section we study Moses Schönfinkel's combinator calculus
\cite{Schönfinkel1924} which provides a way to make local definitions
first order via higher order function space. The language described
here can do more than Def (Section \ref{sec:def}) as it has function
space, so it is closer to the language STT (Chapter
\ref{ch:STT}). Lambda terms can be converted to combinatory terms
which have some extra equations that we don't describe here, see
\cite{DBLP:conf/fscd/AltenkirchKSV23}.

The combinator calculus was the earliest description of universal
computation, more than ten years before Church's lambda calculus
\cite{Church1936AnUP} and Turing machines
\cite{https://doi.org/10.1112/plms/s2-42.1.230}. It avoids the usage
of contexts and variables which makes its definition much simpler,
compare it with the substitution calculus of Section \ref{sec:def}
corresponding to lambda calculus. However writing (and reading!)
programs in SK is much harder than using lambda calculus. Here we
present the simply typed variant of combinator calculus with one base
type \verb$ι$.

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module SK where

open import Lib

module I where
  infixr 5 _⇒_
  infixl 5 _$_

  data Ty : Set where
    ι   : Ty
    _⇒_ : Ty → Ty → Ty

  postulate
    Tm  : Ty → Set
    _$_ : ∀{A B} → Tm (A ⇒ B) → Tm A → Tm B
    K   : ∀{A B} → Tm (A ⇒ B ⇒ A)
    S   : ∀{A B C} → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    Kβ  : ∀{A B}{t : Tm A}{u : Tm B} → K $ t $ u ≡ t
    Sβ  : ∀{A B C}{t : Tm (A ⇒ B ⇒ C)}{u : Tm (A ⇒ B)}{v : Tm A} → S $ t $ u $ v ≡ t $ v $ (u $ v)
\end{code}
An SK model consists of two sorts (types and term), two type operations, three term operations and two term equations.
\begin{code}
record Model {i j} : Set (lsuc (i ⊔ j)) where
  infixr 5 _⇒_
  infixl 5 _$_

  field
    Ty  : Set i
    ι   : Ty
    _⇒_ : Ty → Ty → Ty
    Tm  : Ty → Set j
    _$_ : ∀{A B}    → Tm (A ⇒ B) → Tm A → Tm B
    K   : ∀{A B}    → Tm (A ⇒ B ⇒ A)
    S   : ∀{A B C}  → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    Kβ  : ∀{A B}{t : Tm A}{u : Tm B} → K $ t $ u ≡ t
    Sβ  : ∀{A B C}{t : Tm (A ⇒ B ⇒ C)}{u : Tm (A ⇒ B)}{v : Tm A} →
          S $ t $ u $ v ≡ t $ v $ (u $ v)
\end{code}
\begin{code}[hide]
  ⟦_⟧T    : I.Ty → Ty
  ⟦ I.ι      ⟧T = ι
  ⟦ A I.⇒ B  ⟧T = ⟦ A ⟧T ⇒ ⟦ B ⟧T
  
  postulate
    ⟦_⟧t  : ∀{A} → I.Tm A → Tm ⟦ A ⟧T
    ⟦$⟧t  : ∀{A B}{t : I.Tm (A I.⇒ B)}{u : I.Tm A} → ⟦ t I.$ u ⟧t ≈ ⟦ t ⟧t $ ⟦ u ⟧t
    ⟦K⟧t  : ∀{A B} → ⟦ I.K {A} {B} ⟧t ≈ K {⟦ A ⟧T} {⟦ B ⟧T}
    ⟦S⟧t  : ∀{A B C} → ⟦ I.S {A} {B} {C} ⟧t ≈ S {⟦ A ⟧T} {⟦ B ⟧T}{⟦ C ⟧T}
    {-# REWRITE ⟦$⟧t ⟦K⟧t ⟦S⟧t #-}

record DepModel {i j : Level} : Set (lsuc (i ⊔ j)) where
  infixr 5 _⇒∙_
  infixl 5 _$∙_

  field
    Ty∙  : I.Ty → Set i
    ι∙   : Ty∙ I.ι
    _⇒∙_ : ∀{A B} → Ty∙ A → Ty∙ B → Ty∙ (A I.⇒ B)
    Tm∙  : ∀{A} → Ty∙ A → I.Tm A → Set j
    _$∙_ : ∀{A B}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm (A I.⇒ B)}{u : I.Tm A} →
          Tm∙ (A∙ ⇒∙ B∙) t → Tm∙ A∙ u → Tm∙ B∙ (t I.$ u)
    K∙   : ∀{A B}{A∙ : Ty∙ A}{B∙ : Ty∙ B} → Tm∙ (A∙ ⇒∙ B∙ ⇒∙ A∙) I.K
    S∙   : ∀{A B C}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{C∙ : Ty∙ C} →
          Tm∙ ((A∙ ⇒∙ B∙ ⇒∙ C∙) ⇒∙ (A∙ ⇒∙ B∙) ⇒∙ A∙ ⇒∙ C∙) I.S
    Kβ∙  : ∀{A B}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm A}{u : I.Tm B}{t∙ : Tm∙ A∙ t}{u∙ : Tm∙ B∙ u} → ((Tm∙ A∙) ~) I.Kβ (K∙ $∙ t∙ $∙ u∙) t∙
    Sβ∙  : ∀{A B C}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{C∙ : Ty∙ C}{t : I.Tm (A I.⇒ B I.⇒ C)}{u : I.Tm (A I.⇒ B)}{v : I.Tm A}{t∙ : Tm∙ (A∙ ⇒∙ B∙ ⇒∙ C∙) t}{u∙ : Tm∙ (A∙ ⇒∙ B∙) u}{v∙ : Tm∙ A∙ v} →
          ((Tm∙ C∙) ~) I.Sβ (S∙ $∙ t∙ $∙ u∙ $∙ v∙) ((t∙ $∙ v∙) $∙ (u∙ $∙ v∙))

  ⟦_⟧T : (A : I.Ty) → Ty∙ A
  ⟦ I.ι ⟧T = ι∙
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒∙ ⟦ B ⟧T
  
  postulate
    ⟦_⟧t : ∀{A}(t : I.Tm A) → Tm∙ ⟦ A ⟧T t
    ⟦$⟧t : ∀{A B}{t : I.Tm (A I.⇒ B)}{u : I.Tm A} → ⟦ t I.$ u ⟧t ≈ ⟦ t ⟧t $∙ ⟦ u ⟧t
    ⟦K⟧t : ∀{A B} → ⟦ I.K {A} {B} ⟧t ≈ K∙ {A} {B} {⟦ A ⟧T} {⟦ B ⟧T}
    ⟦S⟧t : ∀{A B C} → ⟦ I.S {A} {B} {C} ⟧t ≈ S∙ {A} {B} {C} {⟦ A ⟧T} {⟦ B ⟧T}{⟦ C ⟧T}
    {-# REWRITE ⟦$⟧t ⟦K⟧t ⟦S⟧t #-}
\end{code}
The \verb$I$ combinator can be derived (here we call it \verb$I'$ to distinguish from the initial model).
\begin{code}[hide]
module _ where
  open I
\end{code}
\begin{code}
  I' : ∀{A} → Tm (A ⇒ A)
  I' {A} = S $ K $ K {A}{ι}

  Iβ : ∀{A}{u : Tm A} → I' $ u ≡ u
  Iβ {A}{u} =
    I' $ u
                                  ≡⟨ refl ⟩
    S $ K $ K $ u
                                  ≡⟨ Sβ ⟩
    K $ u $ (K $ u)
                                  ≡⟨ Kβ ⟩
    u
                                  ∎
\end{code}
Another famous combinator is \verb$B$ (which we call \verb$B'$).
\begin{code}
  B' : ∀{A B C} →  Tm ((B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  B' = S $ (K $ S) $ K

  Bβ : ∀{A B C}{t : Tm (B ⇒ C)}{u : Tm (A ⇒ B)}{v : Tm A} → B' $ t $ u $ v ≡ t $ (u $ v)
  Bβ {t = t}{u = u}{v = v} =
    B' $ t $ u $ v
                                  ≡⟨ refl ⟩
    S $ (K $ S) $ K $ t $ u $ v
                                  ≡⟨ cong {A = Tm _} (λ x → x $ u $ v) Sβ ⟩
    K $ S $ t $ (K $ t) $ u $ v
                                  ≡⟨ cong {A = Tm _} (λ x → x $ (K $ t) $ u $ v) Kβ ⟩
    S $ (K $ t) $ u $ v
                                  ≡⟨ Sβ ⟩
    K $ t $ v $ (u $ v)
                                  ≡⟨ cong {A = Tm _} (λ x → x $ (u $ v)) Kβ ⟩
    t $ (u $ v)
                                  ∎
\end{code}
The standard model.
\begin{code}
St : Model
St = record
  { Ty  = Set
  ; Tm  = λ A → A
  ; ι   = Lift ⊤
  ; _⇒_ = λ A B → A → B
  ; _$_ = λ f x → f x
  ; K   = λ x y → x
  ; S   = λ x y z → x z (y z)
  ; Kβ  = refl
  ; Sβ  = refl
  }
module St = Model St
\end{code}

Normal forms are given as an inductive predicate over terms (as
opposed to Subsection \ref{sec:def-normalisation} where they are
defined as sets together with a functions into terms -- the two
representations are related by the family--map correspondance, see
\cite[p.~221]{gat}).

A term is in normal form if it is a partial application of either
\verb$K$ or \verb$S$. A full application of \verb$K$ has two
arguments, a full application of \verb$S$ has three arguments (and
they are equal to some other term using the equations \verb$Kβ$ and
\verb$Sβ$).
\begin{code}
open I
data Nf : (A : I.Ty) → I.Tm A → Set where
  K₀ : ∀{A B} → Nf (A ⇒ B ⇒ A) K
  K₁ : ∀{A B t} → Nf A t → Nf (B ⇒ A) (K $ t)
  S₀ : ∀{A B C} → Nf ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) S
  S₁ : ∀{A B C t} → Nf (A ⇒ B ⇒ C) t → Nf ((A ⇒ B) ⇒ A ⇒ C) (S $ t)
  S₂ : ∀{A B C t u} → Nf (A ⇒ B ⇒ C) t → Nf (A ⇒ B) u → Nf (A ⇒ C) (S $ t $ u)
\end{code}

The recursive normalisation in Section \ref{sec:def} does not work,
because we cannot define application \verb._$_. on normal forms: we
would need something like \verb.S₂ t u $ v = t $ v $ (u $ v)., but we
only have \verb.t $ u. and \verb.u $ v. in the model.

The solution is Tait's method of \emph{logical predicates} \cite{DBLP:journals/jsyml/Tait67}: we define
predicates on terms by induction on types, together with a function
called \emph{reification} wich says that if a predicate holds for a
term, then it has a normal form.

For \verb$ι$, the predicate is always false.  For a function \verb$t$
the predicate says that if the predicate holds for an input \verb$u$
then it holds for the output \verb@t I.$ u@, and \verb$t$ has to be in
normal form.
\begin{code}
Norm : DepModel
Norm = record
  { Ty∙   =  λ A → Σ (I.Tm A → Set) λ P → {t : I.Tm A} → P t → Nf A t
  ; Tm∙   =  π₁
  ; ι∙    =  (λ _ → Lift ⊥) , λ where ()
  ; _⇒∙_  =  λ {A}{B} A∙ B∙ →
            (λ t → ({u : I.Tm A} → π₁ A∙ u → π₁ B∙ (t I.$ u)) × Nf (A I.⇒ B) t) , π₂
  ; _$∙_  =  λ t u → π₁ t u
  ; K∙    =  λ {A}{B}{A∙}{B∙} →
            (λ t → (λ u → transp (π₁ A∙) (I.Kβ ⁻¹) t) , K₁ (π₂ A∙ t)) , K₀
  ; S∙    =  λ {_}{_}{_}{_}{_}{C∙} →
            (λ t →  (λ u →  (λ v → transp (π₁ C∙) (I.Sβ ⁻¹) (π₁ (π₁ t v) (π₁ u v))
                            ) , S₂ (π₂ t) (π₂ u)
                    ) , S₁ (π₂ t)
            ) , S₀
  ; Kβ∙   =  λ {A}{B}{A∙}{B∙}{t}{u}{t∙}{u∙} → transptransp (π₁ A∙) (Kβ ⁻¹) {Kβ}
  ; Sβ∙   =  λ {A}{B}{C}{A∙}{B∙}{C∙}{t}{u}{v}{t∙}{u∙}{v∙} → transptransp (π₁ C∙)(Sβ ⁻¹){Sβ}
  }
\end{code}
Note that \verb$Norm$ makes use of all the five ways to form normal forms and both
equations in our language. To normalise a term of type \verb$A$, we first interpret
the type in the \verb$Norm$ dependent model. This results in a pair where the second
component is the reification function which produces a normal form from any term for
which the predicate holds. Interpreting the term in \verb$Norm$ gives us a witness
of the predicate. We put together these as follows.
\begin{code}[hide]
module Norm = DepModel Norm
\end{code}
\begin{code}
norm : ∀{A}(t : I.Tm A) → Nf A t
norm {A} t = π₂ Norm.⟦ A ⟧T Norm.⟦ t ⟧t

test : ∀{A B}(u : I.Tm A) → norm (I.K {A}{B} I.$ u) ≡ K₁ (norm u)
test u = refl
\end{code}
We prove completeness by another induction.
Stability is proven by induction on normal forms.
\begin{code}
stab : ∀{A t}(n : Nf A t) → norm t ≡ n
stab K₀         = refl
stab (K₁ n)     = cong K₁ (stab n)
stab S₀         = refl
stab (S₁ n)     = cong S₁ (stab n)
stab (S₂ n n')  = cong (λ w → S₂ (π₁ w) (π₂ w)) (stab n ,×= stab n')
\end{code}
\begin{code}[hide]
infix 4 _≟Ty_ _≟_ 
\end{code}
Decidability of equality of normal forms is proven by double-induction on types and normal forms.
\begin{code}
_≟Ty_  : (A B : Ty) → Dec (Lift (A ≡ B))
_≟_    : ∀{A₀ A₁ t₀ t₁}(v₀ : Nf A₀ t₀)(v₁ : Nf A₁ t₁) →
  Dec (Lift (_≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁)))
\end{code}
\begin{code}[hide]
⇒-cong : ∀{A₀ A₁ B₀ B₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → A₀ ⇒ B₀ ≡ A₁ ⇒ B₁
⇒-cong refl refl = refl

⇒-inj₁ : ∀{A₀ A₁ B₀ B₁} → A₀ ⇒ B₀ ≡ A₁ ⇒ B₁ → A₀ ≡ A₁
⇒-inj₁ refl = refl
⇒-inj₂ : ∀{A₀ A₁ B₀ B₁} → A₀ ⇒ B₀ ≡ A₁ ⇒ B₁ → B₀ ≡ B₁
⇒-inj₂ refl = refl

ι       ≟Ty ι        = ι₁ (mk refl)
ι       ≟Ty _ ⇒ _    = ι₂ (mk λ { (mk ()) })
_ ⇒ _   ≟Ty ι        = ι₂ (mk λ { (mk ()) })
A₀ ⇒ B₀ ≟Ty A₁ ⇒ B₁  with A₀ ≟Ty A₁
A₀ ⇒ B₀ ≟Ty A₁ ⇒ B₁ | ι₁ eA with B₀ ≟Ty B₁
A₀ ⇒ B₀ ≟Ty A₁ ⇒ B₁ | ι₁ eA | ι₁ eB   = ι₁ (mk (⇒-cong (un eA) (un eB)))
A₀ ⇒ B₀ ≟Ty A₁ ⇒ B₁ | ι₁ eA | ι₂ ne   = ι₂ (mk λ e → un ne (mk (⇒-inj₂ (un e))))
A₀ ⇒ B₀ ≟Ty A₁ ⇒ B₁ | ι₂ ne           = ι₂ (mk λ e → un ne (mk (⇒-inj₁ (un e))))

K₀-cong : ∀{A₀ A₁ B₀ B₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ ⇒ A₀ , K , K₀ {A₀}{B₀}) (A₁ ⇒ B₁ ⇒ A₁ , K , K₀ {A₁}{B₁})
K₀-cong refl refl = refl  
K₀-inj₀ : ∀{A₀ A₁ B₀ B₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ ⇒ A₀ , K , K₀ {A₀}{B₀}) (A₁ ⇒ B₁ ⇒ A₁ , K , K₀ {A₁}{B₁}) →
  A₀ ≡ A₁
K₀-inj₀ refl = refl
K₀-inj₁ : ∀{A₀ A₁ B₀ B₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ ⇒ A₀ , K , K₀ {A₀}{B₀}) (A₁ ⇒ B₁ ⇒ A₁ , K , K₀ {A₁}{B₁}) →
  B₀ ≡ B₁
K₀-inj₁ refl = refl

K₁-cong : ∀{A₀ A₁ B₀ B₁}{t₀ : Tm A₀}{t₁ : Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} →
  A₀ ≡ A₁ →
  B₀ ≡ B₁ → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁) →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (B₀ ⇒ A₀ , K $ t₀ , K₁ v₀) (B₁ ⇒ A₁ , K $ t₁ , K₁ v₁)  
K₁-cong refl refl refl = refl
K₁-inj₀ : ∀{A₀ A₁ B₀ B₁}{t₀ : Tm A₀}{t₁ : Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (B₀ ⇒ A₀ , K $ t₀ , K₁ v₀) (B₁ ⇒ A₁ , K $ t₁ , K₁ v₁) →
  A₀ ≡ A₁
K₁-inj₀ refl = refl
K₁-inj₁ : ∀{A₀ A₁ B₀ B₁}{t₀ : Tm A₀}{t₁ : Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (B₀ ⇒ A₀ , K $ t₀ , K₁ v₀) (B₁ ⇒ A₁ , K $ t₁ , K₁ v₁) →
  B₀ ≡ B₁
K₁-inj₁ refl = refl
K₁-inj₂ : ∀{A₀ A₁ B₀ B₁}{t₀ : Tm A₀}{t₁ : Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (B₀ ⇒ A₀ , K $ t₀ , K₁ v₀) (B₁ ⇒ A₁ , K $ t₁ , K₁ v₁) →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁)
K₁-inj₂ refl = refl

S₀-cong : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → C₀ ≡ C₁ → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀ ⇒ C₀) ⇒ (A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S , S₀) ((A₁ ⇒ B₁ ⇒ C₁) ⇒ (A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S , S₀)
S₀-cong refl refl refl = refl  
S₀-inj₀ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀ ⇒ C₀) ⇒ (A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S , S₀) ((A₁ ⇒ B₁ ⇒ C₁) ⇒ (A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S , S₀) →
  A₀ ≡ A₁
S₀-inj₀ refl = refl
S₀-inj₁ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀ ⇒ C₀) ⇒ (A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S , S₀) ((A₁ ⇒ B₁ ⇒ C₁) ⇒ (A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S , S₀) →
  B₀ ≡ B₁
S₀-inj₁ refl = refl
S₀-inj₂ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀ ⇒ C₀) ⇒ (A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S , S₀) ((A₁ ⇒ B₁ ⇒ C₁) ⇒ (A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S , S₀) →
  C₀ ≡ C₁
S₀-inj₂ refl = refl

S₁-cong : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → C₀ ≡ C₁ →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ ⇒ C₀ , t₀ , v₀) (A₁ ⇒ B₁ ⇒ C₁ , t₁ , v₁) →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S $ t₀ , S₁ v₀) ((A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S $ t₁ , S₁ v₁)
S₁-cong refl refl refl refl = refl
S₁-inj₀ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁} → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S $ t₀ , S₁ v₀) ((A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S $ t₁ , S₁ v₁) →
  A₀ ≡ A₁
S₁-inj₀ refl = refl
S₁-inj₁ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁} → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S $ t₀ , S₁ v₀) ((A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S $ t₁ , S₁ v₁) →
  B₀ ≡ B₁
S₁-inj₁ refl = refl
S₁-inj₂ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁} → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S $ t₀ , S₁ v₀) ((A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S $ t₁ , S₁ v₁) →
  C₀ ≡ C₁
S₁-inj₂ refl = refl
S₁-inj₃ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁} → 
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} ((A₀ ⇒ B₀) ⇒ A₀ ⇒ C₀ , S $ t₀ , S₁ v₀) ((A₁ ⇒ B₁) ⇒ A₁ ⇒ C₁ , S $ t₁ , S₁ v₁) →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ ⇒ C₀ , t₀ , v₀) (A₁ ⇒ B₁ ⇒ C₁ , t₁ , v₁)
S₁-inj₃ refl = refl

S₂-cong : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁}{u₀ : Tm (A₀ ⇒ B₀)}{u₁ : Tm (A₁ ⇒ B₁)}{w₀ : Nf (A₀ ⇒ B₀) u₀}{w₁ : Nf (A₁ ⇒ B₁) u₁} →
  A₀ ≡ A₁ → B₀ ≡ B₁ → C₀ ≡ C₁ →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ ⇒ C₀ , t₀ , v₀) (A₁ ⇒ B₁ ⇒ C₁ , t₁ , v₁) →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ , u₀ , w₀) (A₁ ⇒ B₁ , u₁ , w₁) →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ C₀ , S $ t₀ $ u₀ , S₂ v₀ w₀) (A₁ ⇒ C₁ , S $ t₁ $ u₁ , S₂ v₁ w₁)
S₂-cong refl refl refl refl refl = refl
S₂-inj₀ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁}{u₀ : Tm (A₀ ⇒ B₀)}{u₁ : Tm (A₁ ⇒ B₁)}{w₀ : Nf (A₀ ⇒ B₀) u₀}{w₁ : Nf (A₁ ⇒ B₁) u₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ C₀ , S $ t₀ $ u₀ , S₂ v₀ w₀) (A₁ ⇒ C₁ , S $ t₁ $ u₁ , S₂ v₁ w₁) →
  A₀ ≡ A₁
S₂-inj₀ refl = refl
S₂-inj₁ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁}{u₀ : Tm (A₀ ⇒ B₀)}{u₁ : Tm (A₁ ⇒ B₁)}{w₀ : Nf (A₀ ⇒ B₀) u₀}{w₁ : Nf (A₁ ⇒ B₁) u₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ C₀ , S $ t₀ $ u₀ , S₂ v₀ w₀) (A₁ ⇒ C₁ , S $ t₁ $ u₁ , S₂ v₁ w₁) →
  B₀ ≡ B₁
S₂-inj₁ refl = refl
S₂-inj₂ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁}{u₀ : Tm (A₀ ⇒ B₀)}{u₁ : Tm (A₁ ⇒ B₁)}{w₀ : Nf (A₀ ⇒ B₀) u₀}{w₁ : Nf (A₁ ⇒ B₁) u₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ C₀ , S $ t₀ $ u₀ , S₂ v₀ w₀) (A₁ ⇒ C₁ , S $ t₁ $ u₁ , S₂ v₁ w₁) →
  C₀ ≡ C₁
S₂-inj₂ refl = refl
S₂-inj₃ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁}{u₀ : Tm (A₀ ⇒ B₀)}{u₁ : Tm (A₁ ⇒ B₁)}{w₀ : Nf (A₀ ⇒ B₀) u₀}{w₁ : Nf (A₁ ⇒ B₁) u₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ C₀ , S $ t₀ $ u₀ , S₂ v₀ w₀) (A₁ ⇒ C₁ , S $ t₁ $ u₁ , S₂ v₁ w₁) →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ ⇒ C₀ , t₀ , v₀) (A₁ ⇒ B₁ ⇒ C₁ , t₁ , v₁)
S₂-inj₃ refl = refl
S₂-inj₄ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : Tm (A₀ ⇒ B₀ ⇒ C₀)}{t₁ : Tm (A₁ ⇒ B₁ ⇒ C₁)}{v₀ : Nf (A₀ ⇒ B₀ ⇒ C₀) t₀}{v₁ : Nf (A₁ ⇒ B₁ ⇒ C₁) t₁}{u₀ : Tm (A₀ ⇒ B₀)}{u₁ : Tm (A₁ ⇒ B₁)}{w₀ : Nf (A₀ ⇒ B₀) u₀}{w₁ : Nf (A₁ ⇒ B₁) u₁} →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ C₀ , S $ t₀ $ u₀ , S₂ v₀ w₀) (A₁ ⇒ C₁ , S $ t₁ $ u₁ , S₂ v₁ w₁) →
  _≡_ {A = Σ Ty λ A → Σ (Tm A) (Nf A)} (A₀ ⇒ B₀ , u₀ , w₀) (A₁ ⇒ B₁ , u₁ , w₁)
S₂-inj₄ refl = refl

K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} with A₀ ≟Ty A₁
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | ι₁ eA with B₀ ≟Ty B₁
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | ι₁ eA | ι₁ eB = ι₁ (mk (K₀-cong (un eA) (un eB)))
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | ι₁ eA | ι₂ ne = ι₂ (mk λ e → un ne (mk (K₀-inj₁ (un e))))
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | ι₂ ne = ι₂ (mk λ e → un ne (mk (K₀-inj₀ (un e))))
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ with A₀ ≟Ty A₁
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | ι₁ eA with B₀ ≟Ty B₁
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | ι₁ eA | ι₁ eB with v₀ ≟ v₁
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | ι₁ eA | ι₁ eB | ι₁ ev = ι₁ (mk (K₁-cong (un eA) (un eB) (un ev)))
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | ι₁ eA | ι₁ eB | ι₂ ne = ι₂ (mk λ e → un ne (mk (K₁-inj₂ (un e))))
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | ι₁ eA | ι₂ ne = ι₂ (mk λ e → un ne (mk (K₁-inj₁ (un e))))
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | ι₂ ne = ι₂ (mk λ e → un ne (mk (K₁-inj₀ (un e))))
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} with A₀ ≟Ty A₁
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | ι₁ eA with B₀ ≟Ty B₁
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | ι₁ eA | ι₁ eB with C₀ ≟Ty C₁
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | ι₁ eA | ι₁ eB | ι₁ eC = ι₁ (mk (S₀-cong (un eA) (un eB) (un eC)))
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | ι₁ eA | ι₁ eB | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₀-inj₂ (un e))))
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | ι₁ eA | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₀-inj₁ (un e))))
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₀-inj₀ (un e))))
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ with A₀ ≟Ty A₁
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | ι₁ eA with B₀ ≟Ty B₁
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | ι₁ eA | ι₁ eB with C₀ ≟Ty C₁
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | ι₁ eA | ι₁ eB | ι₁ eC with v₀ ≟ v₁
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | ι₁ eA | ι₁ eB | ι₁ eC | ι₁ ev = ι₁ (mk (S₁-cong (un eA) (un eB) (un eC) (un ev)))
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | ι₁ eA | ι₁ eB | ι₁ eC | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₁-inj₃ (un e))))
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | ι₁ eA | ι₁ eB | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₁-inj₂ (un e))))
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | ι₁ eA | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₁-inj₁ (un e))))
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₁-inj₀ (un e))))
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ with A₀ ≟Ty A₁
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA with B₀ ≟Ty B₁
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA | ι₁ eB with C₀ ≟Ty C₁
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA | ι₁ eB | ι₁ eC with v₀ ≟ v₁
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA | ι₁ eB | ι₁ eC | ι₁ ev with w₀ ≟ w₁
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA | ι₁ eB | ι₁ eC | ι₁ ev | ι₁ ew = ι₁ (mk (S₂-cong (un eA) (un eB) (un eC) (un ev) (un ew)))
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA | ι₁ eB | ι₁ eC | ι₁ ev | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₂-inj₄ (un e))))
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA | ι₁ eB | ι₁ eC | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₂-inj₃ (un e))))
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA | ι₁ eB | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₂-inj₂ (un e))))
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₁ eA | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₂-inj₁ (un e))))
S₂ {A₀}{B₀}{C₀} v₀ w₀  ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | ι₂ ne = ι₂ (mk λ e → un ne (mk (S₂-inj₀ (un e))))
K₀     ≟ K₁ _    = ι₂ (mk λ ())
K₀     ≟ S₀      = ι₂ (mk λ ())
K₀     ≟ S₁ _    = ι₂ (mk λ ())
K₀     ≟ S₂ _ _  = ι₂ (mk λ ())
K₁ _   ≟ K₀      = ι₂ (mk λ ())
K₁ _   ≟ S₀      = ι₂ (mk λ ())
K₁ _   ≟ S₁ _    = ι₂ (mk λ ())
K₁ _   ≟ S₂ _ _  = ι₂ (mk λ ())
S₀     ≟ K₀      = ι₂ (mk λ ())
S₀     ≟ K₁ _    = ι₂ (mk λ ())
S₀     ≟ S₁ _    = ι₂ (mk λ ())
S₀     ≟ S₂ _ _  = ι₂ (mk λ ())
S₁ _   ≟ K₀      = ι₂ (mk λ ())
S₁ _   ≟ K₁ _    = ι₂ (mk λ ())
S₁ _   ≟ S₀      = ι₂ (mk λ ())
S₁ _   ≟ S₂ _ _  = ι₂ (mk λ ())
S₂ _ _ ≟ K₀      = ι₂ (mk λ ())
S₂ _ _ ≟ K₁ _    = ι₂ (mk λ ())
S₂ _ _ ≟ S₀      = ι₂ (mk λ ())
S₂ _ _ ≟ S₁ _    = ι₂ (mk λ ())
\end{code}
We obtain decidability of equality for all terms by checking whether the
normal forms are equal.
\begin{code}
_≟Tm_ : ∀{A}(t₀ t₁ : Tm A) → Dec (Lift (t₀ ≡ t₁))
t₀ ≟Tm t₁ with norm t₀ ≟ norm t₁
... | ι₁ e  = ι₁ (mk (congd (λ z → π₁ (π₂ z)) (un e)))
... | ι₂ ne = ι₂ (mk λ e → un ne (mk (cong (λ z → (_ , z , norm z)) (un e))))
\end{code}

TODO: examples of normalisation, sometimes there is an infinite loop (?)
