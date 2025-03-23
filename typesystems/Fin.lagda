\chapter{Product and sum types}
\label{ch:Fin}

\begin{tcolorbox}[title=Learning goals of this chapter]
  Nullary and binary products.
  Nullary and binary sums.
  Applications: enumerations, booleans encoded as sums, option type.
  Types form an exponential rig.
  More equalities in the standard model than in the syntax.
\end{tcolorbox}

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module Fin where

open import Lib

record Model {i j} : Set (lsuc (i ⊔ j)) where
  infixl 6 _[_]
  infixl 5 _▹_
  infixr 6 _⇒_
  infixl 5 _$_
  infixl 7 _×o_
  infixl 5 _,o_
  infixl 6 _+o_

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

    _⇒_    : Ty → Ty → Ty
    lam    : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
    _$_    : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    ⇒β     : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A} → lam t $ u ≡ t [ ⟨ u ⟩ ]
    ⇒η     : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → t ≡ lam (t [ p ] $ var vz)
    lam[]  : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{Δ}{σ : Sub Δ Γ} → lam t [ σ ] ≡ lam (t [ σ ⁺ ])
    $[]    : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{Δ}{σ : Sub Δ Γ} →
             (t $ u) [ σ ] ≡ (t [ σ ]) $ (u [ σ ])
\end{code}
A Fin model consists of the substitution calculus (Def without \verb$Bool$ and \verb$Nat$), components
for function space and components for the following four new type formers.
\begin{itemize}
\item Binary products:
\begin{code}
    _×o_      : Ty → Ty → Ty
    _,o_      : ∀{Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (A ×o B)
    fst       : ∀{Γ A B} → Tm Γ (A ×o B) → Tm Γ A
    snd       : ∀{Γ A B} → Tm Γ (A ×o B) → Tm Γ B
    ×β₁       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → fst (u ,o v) ≡ u
    ×β₂       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → snd (u ,o v) ≡ v
    ×η        : ∀{Γ A B}{t : Tm Γ (A ×o B)} → t ≡ (fst t ,o snd t)
    ,[]       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B}{Δ}{γ : Sub Δ Γ} →
                (u ,o v) [ γ ] ≡ (u [ γ ] ,o v [ γ ])
\end{code}
A term of the binary product type \verb$A ×o B$ (other notations: \verb$A × B$, \verb$record { a : A , b : B }$) is an ordered pair of a
term of type \verb$A$ and another of type \verb$B$. The constructor is
pairing, and there are two destructors: first and second
projections. The computation rules say what happens if we project out
the first or second element of a pair, the uniqueness rule says that
any term of the product type is a pair. We only need a
substitution rule for the constructor, the substitution rules for the
destructors can be proven:
\begin{code}[hide]
  fst[] : ∀{Γ A B}{t : Tm Γ (A ×o B)}{Δ}{γ : Sub Δ Γ} →
    fst t [ γ ] ≡ fst (t [ γ ])
  fst[] {Γ}{A}{B}{t}{Δ}{γ} =
\end{code}
\begin{code}
    fst t [ γ ]
                                       ≡⟨ ×β₁ ⁻¹ ⟩
    fst (fst t [ γ ] ,o snd t [ γ ])
                                       ≡⟨ cong fst (,[] ⁻¹) ⟩
    fst ((fst t ,o snd t) [ γ ])
                                       ≡⟨ cong (λ z → fst (z [ γ ])) (×η ⁻¹) ⟩
    fst (t [ γ ])
                                       ∎
\end{code}
The rules for binary products can be summarised by
the following isomorphism:
\begin{verbatim}
Tm Γ (A ×o B) ≅ Tm Γ A × Tm Γ B
\end{verbatim}
The left to right
direction is given by \verb$fst$ and \verb$snd$, the right to left direction by \verb$_,o_$,
the proofs that the roundtrips are identity are \verb$×β$ and \verb$×η$.
\begin{code}[hide]
  field
\end{code}
\item Nullary products:
\begin{code}
    Unit      : Ty
    trivial   : ∀{Γ} → Tm Γ Unit
    Unitη     : ∀{Γ}{u : Tm Γ Unit} → u ≡ trivial
\end{code}
The nullary product is the unit (top, \verb$()$) type with only one
constructor and no destructor: this shows that there is no information
in a term of type \verb$Unit$, there is no way to use such a
term. This is why in some programming languages this type is called
\verb$void$ -- when a function does not return a value, its return type
is unit. The summarising isomorphism: \verb$Tm Γ Unit ≅ ⊤$.
\item Binary sums:
\begin{code}
    _+o_      : Ty → Ty → Ty
    inl       : ∀{Γ A B} → Tm Γ A → Tm Γ (A +o B)
    inr       : ∀{Γ A B} → Tm Γ B → Tm Γ (A +o B)
    caseo     : ∀{Γ A B C} → Tm (Γ ▹ A) C → Tm (Γ ▹ B) C → Tm Γ (A +o B) → Tm Γ C
    +β₁       : ∀{Γ A B C}{c₁ : Tm (Γ ▹ A) C}{c₂ : Tm (Γ ▹ B) C}{a : Tm Γ A} →
                caseo c₁ c₂ (inl a) ≡ c₁ [ ⟨ a ⟩ ]
    +β₂       : ∀{Γ A B C}{c₁ : Tm (Γ ▹ A) C}{c₂ : Tm (Γ ▹ B) C}{b : Tm Γ B} →
                caseo c₁ c₂ (inr b) ≡ c₂ [ ⟨ b ⟩ ]
    +η        : ∀{Γ A B C}{c : Tm (Γ ▹ A +o B) C} →
                c ≡ caseo  (c [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ] [ p ⁺ ])
                           (c [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ] [ p ⁺ ]) (var vz)
    inl[]     : ∀{Γ A B}{a : Tm Γ A}{Δ}{γ : Sub Δ Γ} → inl {B = B} a [ γ ] ≡ inl (a [ γ ])
    inr[]     : ∀{Γ A B}{b : Tm Γ B}{Δ}{γ : Sub Δ Γ} → inr {A = A} b [ γ ] ≡ inr (b [ γ ])
    case[]    : ∀{Γ A B C}{c₁ : Tm (Γ ▹ A) C}{c₂ : Tm (Γ ▹ B) C}{ab : Tm Γ (A +o B)}
                {Δ}{γ : Sub Δ Γ} →
                (caseo c₁ c₂ ab) [ γ ] ≡ caseo (c₁ [ γ ⁺ ]) (c₂ [ γ ⁺ ]) (ab [ γ ])
\end{code}
\verb$caseo$ binds a variable of type \verb$A$ in its first explicit argument and a variable
of type \verb$B$ in its second explicit argument.
They are specified by the following isomorphism which is natural both in \verb$Γ$ and \verb$C$ (this means that we have substitution laws for both $Γ$ and $C$, see below).
\begin{verbatim}
  (_[p⁺][⟨inl v0⟩], _[p⁺][⟨inr v0⟩]) : Tm (Γ ▹ A +o B) C ≅ Tm (Γ ▹ A) C × Tm (Γ ▹ B) C : caseo
\end{verbatim}
\item Nullary sums:
\begin{code}[hide]
  field
\end{code}
\begin{code}
    Empty     : Ty
    absurd    : ∀{Γ A} → Tm Γ Empty → Tm Γ A
    Emptyη    : ∀{Γ A}{t : Tm (Γ ▹ Empty) A} → t ≡ absurd (var vz)
    absurd[]  : ∀{Γ A}{t : Tm Γ Empty}{Δ}{γ : Sub Δ Γ} →
                absurd {A = A} t [ γ ] ≡ absurd (t [ γ ])
\end{code}
The isomorphism: \verb$Tm (Γ ▹ Empty) A ≅ ⊤$.
\end{itemize}

\begin{code}[hide]
open import Fin.Syntax
\end{code}

\begin{exe}[recommended]
Prove the substitution rule for the other destructor for products.
\textnormal{\begin{code}
snd[] : ∀{Γ A B}{t : Tm Γ (A ×o B)}{Δ}{γ : Sub Δ Γ} → snd t [ γ ] ≡ snd (t [ γ ])
\end{code}}
\begin{code}[hide]
snd[] = exercisep
\end{code}
\end{exe}
\begin{exe}[compulsory]
Prove the substitution rule for the constructor of the unit type.
\textnormal{\begin{code}
trivial[] : ∀{Γ Δ}{γ : Sub Δ Γ} → trivial [ γ ] ≡ trivial
\end{code}}
\begin{code}[hide]
trivial[] = exercisep
\end{code}
\end{exe}
We define the components of the isomorphism for sums, prove that the roundrips are identities and the naturality equations.
\begin{code}
left      : ∀{Γ A B C} → Tm (Γ ▹ A +o B) C → Tm (Γ ▹ A) C
left c = c [ p ⁺ ] [ ⟨ inl v0 ⟩ ]
right     : ∀{Γ A B C} → Tm (Γ ▹ A +o B) C → Tm (Γ ▹ B) C
right c = c [ p ⁺ ] [ ⟨ inr v0 ⟩ ]
case'     : ∀{Γ A B C} → Tm (Γ ▹ A) C → Tm (Γ ▹ B) C → Tm (Γ ▹ A +o B) C
case' c₁ c₂ = caseo (c₁ [ p ⁺ ]) (c₂ [ p ⁺ ]) v0
+η'        : ∀{Γ A B C}{t : Tm (Γ ▹ A +o B) C} →
            t ≡ case' (left t) (right t)
+η' {t = t} =
  t
                                     ≡⟨ +η ⟩
  caseo (t [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ] [ p ⁺ ]) (t [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ] [ p ⁺ ]) (var vz)
                                     ≡⟨ refl ⟩
  case' (left t) (right t)
                                     ∎
+β₁'      : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C} →
            left (case' u v) ≡ u
\end{code}
\begin{code}[hide]
+β₁' {u = u}{v} =
  left (case' u v)
                                     ≡⟨ refl ⟩
  caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ]
                                     ≡⟨ cong (_[ ⟨ inl (var vz) ⟩ ]) case[] ⟩
  caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) (var vz [ p ⁺ ]) [ ⟨ inl (var vz) ⟩ ]
                                     ≡⟨ cong (λ z → caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) z [ ⟨ inl (var vz) ⟩ ]) vz[⁺] ⟩
  caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) (var vz) [ ⟨ inl (var vz) ⟩ ]
                                     ≡⟨ case[] ⟩
  caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (var vz [ ⟨ inl (var vz) ⟩ ])
                                     ≡⟨ cong (caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ])) vz[⟨⟩] ⟩
  caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (inl (var vz))
                                     ≡⟨ +β₁ ⟩
  u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ]
                                     ≡⟨ cong (λ z → z [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ]) [p⁺][⁺⁺] ⟩
  u [ p ⁺ ] [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ]
                                     ≡⟨ cong (_[ ⟨ var vz ⟩ ]) [p⁺][⟨⟩⁺] ⟩
  u [ p ⁺ ] [ ⟨ var vz ⟩ ]
                                     ≡⟨ [p⁺][⟨vz⟩] ⟩
  u
                                     ∎
\end{code}
\begin{code}
[]case    : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{D}{w : Tm (Γ ▹ C) D} →
            w [ p ⁺ ] [ ⟨ case' u v ⟩ ] ≡ case' (w [ p ⁺ ] [ ⟨ u ⟩ ]) (w [ p ⁺ ] [ ⟨ v ⟩ ])
\end{code}
\begin{code}[hide]
[]case {u = u}{v}{w = w} =
  w [ p ⁺ ] [ ⟨ case' u v ⟩ ]
                                     ≡⟨ refl ⟩
  w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) ⟩ ]
                                     ≡⟨ +η ⟩
  caseo (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) ⟩ ] [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) ⟩ ] [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (x [ ⟨ inl (var vz) ⟩ ] [ p ⁺ ]) (y [ ⟨ inr (var vz) ⟩ ] [ p ⁺ ]) (var vz)) [⟨⟩][] [⟨⟩][] ⟩
  caseo (w [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] ⟩ ] [ ⟨ inl (var vz) ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] ⟩ ] [ ⟨ inr (var vz) ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (x [ p ⁺ ]) (y [ p ⁺ ]) (var vz)) [⟨⟩][] [⟨⟩][] ⟩
  caseo (w [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (x [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ]) (y [ ⟨ inr (var vz) ⟩ ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ]) (var vz)) [p⁺][⁺⁺] [p⁺][⁺⁺] ⟩
  caseo (w [ p ⁺ ] [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (x [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ]) (y [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ]) (var vz)) [p⁺][⟨⟩⁺] [p⁺][⟨⟩⁺] ⟩
  caseo (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ]) (v [ p ⁺ ]) (var vz) [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (w [ p ⁺ ] [ ⟨ x [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ y [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ]) (var vz)) case[] case[] ⟩
  caseo (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) (var vz [ p ⁺ ]) [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) (var vz [ p ⁺ ]) [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) x [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) y [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ]) (var vz)) vz[⁺] vz[⁺] ⟩
  caseo (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) (var vz) [ ⟨ inl (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ]) (var vz) [ ⟨ inr (var vz) ⟩ ] ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (w [ p ⁺ ] [ ⟨ x ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ y ⟩ ] [ p ⁺ ]) (var vz)) case[] case[] ⟩
  caseo (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (var vz [ ⟨ inl (var vz) ⟩ ]) ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ]) (var vz [ ⟨ inr (var vz) ⟩ ]) ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) x ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ]) y ⟩ ] [ p ⁺ ]) (var vz)) vz[⟨⟩] vz[⟨⟩] ⟩
  caseo (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ]) (inl (var vz)) ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ caseo (u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ]) (v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ]) (inr (var vz)) ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (w [ p ⁺ ] [ ⟨ x ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ y ⟩ ] [ p ⁺ ]) (var vz)) +β₁ +β₂ ⟩
  caseo (w [ p ⁺ ] [ ⟨ u [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ v [ p ⁺ ] [ p ⁺ ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (w [ p ⁺ ] [ ⟨ x [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ y [ ⟨ inr (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ]) (var vz)) [p⁺][⁺⁺] [p⁺][⁺⁺] ⟩
  caseo (w [ p ⁺ ] [ ⟨ u [ p ⁺ ] [ p ⁺ ] [ ⟨ inl (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ v [ p ⁺ ] [ p ⁺ ] [ ⟨ inr (var vz) ⟩ ⁺ ] [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (w [ p ⁺ ] [ ⟨ x [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ y [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ]) (var vz)) [p⁺][⟨⟩⁺] [p⁺][⟨⟩⁺] ⟩
  caseo (w [ p ⁺ ] [ ⟨ u [ p ⁺ ] [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ])
        (w [ p ⁺ ] [ ⟨ v [ p ⁺ ] [ ⟨ var vz ⟩ ] ⟩ ] [ p ⁺ ])
        (var vz)
                                     ≡⟨ cong₂ (λ x y → caseo (w [ p ⁺ ] [ ⟨ x ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ y ⟩ ] [ p ⁺ ]) (var vz)) [p⁺][⟨vz⟩] [p⁺][⟨vz⟩] ⟩
  caseo (w [ p ⁺ ] [ ⟨ u ⟩ ] [ p ⁺ ]) (w [ p ⁺ ] [ ⟨ v ⟩ ] [ p ⁺ ]) (var vz)
                                     ≡⟨ refl ⟩
  case' (w [ p ⁺ ] [ ⟨ u ⟩ ]) (w [ p ⁺ ] [ ⟨ v ⟩ ])
                                     ∎
\end{code}
\begin{code}
+β₂'       : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C} →
            right (case' u v) ≡ v
\end{code}
\begin{code}[hide]
+β₂' = exercisep
\end{code}
\begin{code}
case[]'    : ∀{Γ A B C}{u : Tm (Γ ▹ A) C}{v : Tm (Γ ▹ B) C}{Δ}{γ : Sub Δ Γ} →
            (case' u v) [ γ ⁺ ] ≡
            case' (u [ γ ⁺ ]) (v [ γ ⁺ ])
\end{code}
\begin{code}[hide]
case[]' = exercisep
\end{code}
\begin{code}
[]left    : ∀{Γ A B C}{t : Tm (Γ ▹ A +o B) C}{D}{w : Tm (Γ ▹ C) D} →
            w [ p ⁺ ] [ ⟨ left t ⟩ ] ≡ left (w [ p ⁺ ] [ ⟨ t ⟩ ])
[]left = exercisep
\end{code}
\begin{code}
[]right   : ∀{Γ A B C}{t : Tm (Γ ▹ A +o B) C}{D}{w : Tm (Γ ▹ C) D} →
            w [ p ⁺ ] [ ⟨ right t ⟩ ] ≡ right (w [ p ⁺ ] [ ⟨ t ⟩ ])
\end{code}
\begin{code}[hide]
[]right = exercisep
\end{code}
\begin{code}
left[]  : ∀{Γ A B C}{t : Tm (Γ ▹ A +o B) C}{Δ}{γ : Sub Δ Γ} →
          left t [ γ ⁺ ] ≡ left (t [ γ ⁺ ])
\end{code}
\begin{code}[hide]
left[] {Γ}{A}{B}{C}{t}{Δ}{γ} =
  left t [ γ ⁺ ]
                                            ≡⟨ +β₁' ⁻¹ ⟩
  left (case' (left t [ γ ⁺ ]) (right t [ γ ⁺ ]))
                                            ≡⟨ cong left (case[]' ⁻¹) ⟩
  left (case' (left t) (right t) [ γ ⁺ ])
                                            ≡⟨ cong (λ z → left (z [ γ ⁺ ])) (+η' ⁻¹) ⟩
  left (t [ γ ⁺ ])
                                            ∎
\end{code}

\section{Applications}

Enumerations can be defined using the unit and sum types. For example, the type with three elements:
\begin{code}
Three : Ty
Three = Unit +o (Unit +o Unit)
\end{code}
Its three elements:
\begin{code}
three0 three1 three2 : ∀{Γ} → Tm Γ Three
three0 = inl trivial
three1 = inr (inl trivial)
three2 = inr (inr trivial)
\end{code}
Elimination principle of \verb$Three$.
\begin{exe}[recommended]
The second and third rules are exercises.
\textnormal{\begin{code}
caseThree : ∀{Γ A} → Tm Γ Three → Tm Γ A → Tm Γ A → Tm Γ A → Tm Γ A
caseThree t u v w = caseo (u [ p ]) (caseo (v [ p ] [ p ]) (w [ p ] [ p ]) v0) t
Threeβ0 : ∀{Γ A}{u v w : Tm Γ A} → caseThree three0 u v w ≡ u
Threeβ1 : ∀{Γ A}{u v w : Tm Γ A} → caseThree three1 u v w ≡ v
Threeβ2 : ∀{Γ A}{u v w : Tm Γ A} → caseThree three2 u v w ≡ w
Threeβ0 {Γ}{a}{u}{v}{w} =
  caseThree three0 u v w
                         ≡⟨ refl ⟩
  caseo (u [ p ]) (caseo (v [ p ] [ p ]) (w [ p ] [ p ]) v0) (inl trivial)
                         ≡⟨ +β₁ ⟩
  u [ p ] [ ⟨ trivial ⟩ ]
                         ≡⟨ [p][⟨⟩] ⟩
  u
                         ∎
\end{code}
\begin{code}[hide]
Threeβ1 = exercisep
Threeβ2 = exercisep
\end{code}}
\end{exe}
Addition modulo 3:
\begin{code}
plus3 : Tm ◇ (Three ⇒ Three ⇒ Three)
plus3 = lam (lam (caseThree v1
  {- v1=0 -} v0
  {- v1=1 -} (caseThree v0 three1 three2 three0)
  {- v1=2 -} (caseThree v0 three2 three0 three1)))
\end{code}
\begin{exe}
Prove the computation rules for \verb$plus3$.
\textnormal{\begin{code}
plus3test00 : plus3 $ three0 $ three0 ≡ three0
plus3test11 : plus3 $ three1 $ three1 ≡ three2
plus3test12 : plus3 $ three1 $ three2 ≡ three0
\end{code}}
\begin{code}[hide]
plus3test00 = exercisep
plus3test11 = exercisep
plus3test12 = exercisep
\end{code}
\end{exe}
We define booleans. The usual eliminator (if-then-else) is defined using case.
\begin{code}
Bool : Ty
Bool = Unit +o Unit

true : ∀{Γ} → Tm Γ Bool
true = inl trivial

false : ∀{Γ} → Tm Γ Bool
false = inr trivial

ite : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
ite b u v = caseo (u [ p ]) (v [ p ]) b
Boolβ₁ : ∀{Γ A}{u v : Tm Γ A} → ite true u v ≡ u
Boolβ₁ {Γ}{A}{u}{v} =
  ite true u v
    ≡⟨ refl ⟩
  caseo (u [ p ]) (v [ p ]) (inl trivial)
    ≡⟨ +β₁ ⟩
  u [ p ] [ ⟨ trivial ⟩ ]
    ≡⟨ [p][⟨⟩] ⟩
  u
    ∎
\end{code}
\begin{exe}
Prove the other computation rule.
\textnormal{\begin{code}
Boolβ₂ : ∀{Γ A}{u v : Tm Γ A} → ite false u v ≡ v
\end{code}}
\begin{code}[hide]
Boolβ₂ = exercisep
\end{code}
\end{exe}
\begin{exe}
Prove the following uniqueness rule for booleans.
\textnormal{\begin{code}
Boolη : ∀{Γ A}{t : Tm (Γ ▹ Bool) A} → t ≡ ite v0 (t [ ⟨ true ⟩ ] [ p ]) (t [ ⟨ false ⟩ ] [ p ])
\end{code}}
\begin{code}[hide]
Boolη = exercisep
\end{code}
\end{exe}
\begin{exe}
With the help of \verb$Boolη$, show that the following two implementations of negation are equal.
\textnormal{\begin{code}
ors= : lam {◇} (ite v0 false true) ≡ lam (ite v0 false (ite v0 true true))
\end{code}}
\begin{code}[hide]
ors= = exercisep
\end{code}
\end{exe}
\begin{exe}[hard]
Show that there are only four functions in \verb$Tm ◇ (Bool ⇒ Bool)$!
\end{exe}

With \verb$Bool$ and binary products we can simulate homogeneous binary sums:
\begin{code}
2*_ : Ty → Ty
2* A = Bool ×o A
inl' inr' : ∀{Γ A} → Tm Γ A → Tm Γ (2* A)
inl' t = (true ,o t)
inr' t = (false ,o t)
case2 : ∀{Γ A C} → Tm Γ (2* A) → Tm (Γ ▹ A) C → Tm (Γ ▹ A) C → Tm Γ C
case2 t u v = ite (fst t) (u [ ⟨ snd t ⟩ ]) (v [ ⟨ snd t ⟩ ])
2*β₁ : ∀{Γ A C}{t : Tm Γ A}{u v : Tm (Γ ▹ A) C} → case2 (inl' t) u v ≡ u [ ⟨ t ⟩ ]
2*β₁ {Γ}{A}{C}{t}{u}{v} =
  case2 (inl' t) u v
    ≡⟨ refl ⟩
  ite (fst (true ,o t)) (u [ ⟨ snd (inl' t) ⟩ ]) (v [ ⟨ snd (inl' t) ⟩ ])
    ≡⟨ cong (λ x → ite x (u [ ⟨ snd (inl' t) ⟩ ]) (v [ ⟨ snd (inl' t) ⟩ ])) ×β₁ ⟩
  ite true (u [ ⟨ snd (inl' t) ⟩ ]) (v [ ⟨ snd (inl' t) ⟩ ])
    ≡⟨ Boolβ₁ ⟩
  u [ ⟨ snd (inl' t) ⟩ ]
    ≡⟨ refl ⟩
  u [ ⟨ snd (true ,o t) ⟩ ]
    ≡⟨ cong (λ x → u [ ⟨ x ⟩ ]) ×β₂ ⟩
  u [ ⟨ t ⟩ ]
    ∎
\end{code}
\begin{exe}
Prove the other \verb$β$ rule.
\textnormal{\begin{code}
2*β₂ : ∀{Γ A C}{t : Tm Γ A}{u v : Tm (Γ ▹ A) C} → case2 (inr' t) u v ≡ v [ ⟨ t ⟩ ]
\end{code}}
\begin{code}[hide]
2*β₂ = exercisep
\end{code}
\end{exe}
The option type former (sometimes called maybe) adds an extra element to a type:
\begin{code}
Opt : Ty → Ty
Opt A = A +o Unit
none : ∀{Γ A} → Tm Γ (Opt A)
none = inr trivial
some : ∀{Γ A} → Tm Γ A → Tm Γ (Opt A)
some t = inl t
\end{code}
A type with \verb$n$ elements:
\begin{code}
Fino : ℕ → Ty
Fino zero    = Empty
Fino (suc n) = Unit +o Fino n
\end{code}
\begin{exe}
  For each \verb$n$, define the elimination principle of \verb$Fino n$.
\end{exe}
For a natural number \verb$n$, we define \verb$n$-ary products which are parameterised by \verb$n$ types.
\begin{code}
Tys : ℕ → Set
Tys zero     = Raise (Lift ⊤)
Tys (suc n)  = Ty × Tys n

Prod : {n : ℕ} → Tys n → Ty
Prod {zero}  _         = Unit
Prod {suc n} (A , As)  = A ×o Prod As
\end{code}
The constructor takes \verb$n$ terms and turns them into a term.
\begin{code}
Tms : Con → {n : ℕ} → Tys n → Set
Tms Γ {zero}  _         = Raise (Lift ⊤)
Tms Γ {suc n} (A , As)  = Tm Γ A × Tms Γ As

tpl : ∀{Γ n}{As : Tys n} → Tms Γ As → Tm Γ (Prod As)
tpl {Γ} {zero}   _         = trivial
tpl {Γ} {suc n}  (t , ts)  = (t ,o tpl ts)
\end{code}
We have \verb$n$ different projections.
\begin{code}
_!_ : ∀{n} → Tys n → Fin n → Ty
(A , As) ! zero   = A
(A , As) ! suc i  = As ! i

prj : ∀{Γ n}{As : Tys n}(i : Fin n) → Tm Γ (Prod As) → Tm Γ (As ! i)
prj zero     t = fst t
prj (suc i)  t = prj i (snd t)
\end{code}
\begin{exe}
State and prove the computation rules and the substitution laws.
\end{exe}
\begin{exe}
Define \verb$n$-ary coproducts.
\end{exe}

\section{Algebraic properties of types}

Types form a commutative exponential semiring (commutative exponential rig) up to isomorphism. Isomorphism of two types is defined as follows.
\begin{code}[hide]
\end{code}
\begin{code}
record _≅_ (A B : Ty) : Set where
  field
    f  : Tm (◇ ▹ A) B
    g  : Tm (◇ ▹ B) A
    fg : f [ p ⁺ ] [ ⟨ g ⟩ ] ≡ v0
    gf : g [ p ⁺ ] [ ⟨ f ⟩ ] ≡ v0
open _≅_
infix 4 _≅_
\end{code}
\begin{exe}[compulsory]
  Show that for any type \verb$A$, \verb$A ×o Unit$ is isormophic to \verb$A$.
\textnormal{\begin{code}
×idr : ∀{A} → A ×o Unit ≅ A
\end{code}}
\begin{code}[hide]
×idr = exercise
\end{code}
\end{exe}
\begin{exe}[compulsory]
  Show that for any two types \verb$A$, \verb$B$, there is an isomorphism between \verb$A +o B$ and \verb$B +o A$.
\textnormal{\begin{code}
+ocomm : ∀{A B} → A +o B ≅ B +o A
\end{code}}
\begin{code}[hide]
+ocomm = exercise
\end{code}
\end{exe}
The following exercise is a type theoretic version of the algebraic equation \verb$(a+b)² = a² + 2*a*b + b²$.
\begin{exe}[compulsory]
  Show that for any two types \verb$A$, \verb$B$, there is an isomorphism between \verb$(Unit +o Unit) ⇒ (A +o B)$ and \verb$((Unit +o Unit) ⇒ A +o (Unit +o Unit) ×o A ×o B) +o (Unit +o Unit) ⇒ B$. At least define the first two components (\verb$f$ and \verb$g$).
\end{exe}
\begin{exe}[some parts are compulsory]
  Show that up to isomorphism \verb$_≅_$, types form a commutative exponential semiring (exponential rig).
\end{exe}

\section{Standard model}

\begin{code}[hide]
St : Model
St = record
  { Ty        = Set
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
  ; _⇒_       = λ A B → A → B
  ; lam       = λ t γ → λ a → t (γ , a)
  ; _$_       = λ t u γ → t γ (u γ)
  ; ⇒β        = refl
  ; ⇒η        = refl
  ; lam[]     = refl
  ; $[]       = refl  
\end{code}
The new components:
\begin{code}
  ; _×o_      = _×_
  ; _,o_      = λ a b γ → a γ , b γ
  ; fst       = λ ab γ → π₁ (ab γ)
  ; snd       = λ ab γ → π₂ (ab γ)
  ; ×β₁       = refl
  ; ×β₂       = refl
  ; ×η        = refl
  ; ,[]       = refl
  ; Unit      = Lift ⊤
  ; trivial   = _
  ; Unitη     = refl
  ; _+o_      = _⊎_
  ; inl       = λ a γ → ι₁ (a γ)
  ; inr       = λ b γ → ι₂ (b γ)
  ; caseo     = λ c₁ c₂ ab γ → case (ab γ) (λ a → c₁ (γ , a)) (λ b → c₂ (γ , b))
  ; +β₁       = refl
  ; +β₂       = refl
  ; +η        = funext λ { (_ , ι₁ _) → refl ; (_ , ι₂ _) → refl }
  ; inl[]     = refl
  ; inr[]     = refl
  ; case[]    = refl
  ; Empty     = Lift ⊥
  ; absurd    = λ t γ → exfalso (un (t γ))
  ; Emptyη    = funext λ ()
  ; absurd[]  = refl
\end{code}
\begin{code}[hide]
  }
\end{code}
Some equalities of the standard model are not definitional: those which are not implemented
in the metatheory (Agda).

Some equalities which hold in the standard model are not present in the syntax, for example:
\begin{code}[hide]
module EqualitiesInSt where
module St = Model St
\end{code}
\begin{code}
e1 : St.Con ≡ St.Ty
e2 : ∀{Γ Δ} → St.Sub Δ Γ ≡ St.Tm Δ Γ
e4 : ∀{Γ A Δ} → _≡_ {A = St.Sub Δ (Γ St.▹ A) → St.Tm Δ A} (St.var St.vz St.[_]) St.snd
e5 : ∀{A} → St.Tm St.◇ (St.Unit St.×o A) ≡ St.Sub St.◇ (St.◇ St.▹ A)
\end{code}
\begin{code}[hide]
e1 = refl {A = Set₁}
e2 = refl {A = Set}
e4 {Γ}{A}{Δ} = refl {A = (Δ → Γ × A) → Δ → A}
e5 {A} = refl {A = Set}
\end{code}

TODO: normalisation. what are normal forms?

% \begin{code}[hide]
% open I
% \end{code}
% \begin{code}
% data Var : Con → Ty → Set where
%   vz : ∀{Γ A} → Var (Γ ▹ A) A
%   vs : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A
% 
% data Ne (Γ : Con) : Ty → Set
% data Nf (Γ : Con) : Ty → Set
% 
% data Ne Γ where
%   var       : ∀{A} → Var Γ A → Ne Γ A
%   _$Ne_     : ∀{A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
%   fstNe     : ∀{A B} → Ne Γ (A ×o B) → Ne Γ A
%   sndNe     : ∀{A B} → Ne Γ (A ×o B) → Ne Γ B
%   caseNe    : ∀{A B C} → Nf (Γ ▹ A) C → Nf (Γ ▹ B) C → Ne Γ (A +o B) → Ne Γ C
%   exfalso   : Ne Γ Empty → Ne Γ A
%
% data Nf Γ where
%   lamNf     : ∀{A B} → Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
%   ⟨_,_⟩Nf   : ∀{A B} → Nf Γ A → Nf Γ B → Nf Γ (A ×o B)
%   trivialNf : Nf Γ Unit
%   inlNf     : ∀{A B} → Nf Γ A → Nf Γ (A +o B)
%   inrNf     : ∀{A B} → Nf Γ B → Nf Γ (A +o B)
% TODO: mi a normal formaja "lam (q $ trivial)"-nak?
% \end{code}
% \begin{code}
% ⌜_⌝V : ∀{Γ A} → Var Γ A → Tm Γ A
% \end{code}
% \begin{code}[hide]
% ⌜ vz ⌝V = q
% ⌜ vs x ⌝V = ⌜ x ⌝V [ p ]
% \end{code}
% \begin{code}
% ⌜_⌝Ne : ∀{Γ A} → Ne Γ A → Tm Γ A
% ⌜_⌝Nf : ∀{Γ A} → Nf Γ A → Tm Γ A
% \end{code}
% \begin{code}[hide]
% ⌜_⌝Ne = exercise
% ⌜_⌝Nf = exercise
% \end{code}
