\chapter{Coinductive types}
\label{ch:Coind}

\begin{tcolorbox}[title=Learning goals of this chapter]
  Coinductive types by example: streams, machines.
\end{tcolorbox}

\begin{code}[hide]
{-# OPTIONS --prop --rewriting --guardedness #-}
open import Lib

module Coind where

module tmp where
  record Model {i j} : Set (lsuc (i ⊔ j)) where
    infixl 6 _[_]
    infixl 5 _▹_
    infixr 6 _⇒_
    infixl 5 _$_
    infixl 7 _×o_
    infixl 5 _,o_
    
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

      _×o_      : Ty → Ty → Ty
      _,o_      : ∀{Γ A B} → Tm Γ A → Tm Γ B → Tm Γ (A ×o B)
      fst       : ∀{Γ A B} → Tm Γ (A ×o B) → Tm Γ A
      snd       : ∀{Γ A B} → Tm Γ (A ×o B) → Tm Γ B
      ×β₁       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → fst (u ,o v) ≡ u
      ×β₂       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B} → snd (u ,o v) ≡ v
      ×η        : ∀{Γ A B}{t : Tm Γ (A ×o B)} → t ≡ (fst t ,o snd t)
      ,[]       : ∀{Γ A B}{u : Tm Γ A}{v : Tm Γ B}{Δ}{γ : Sub Δ Γ} →
                  (u ,o v) [ γ ] ≡ (u [ γ ] ,o v [ γ ])

      Bool       : Ty
      true       : ∀{Γ} → Tm Γ Bool
      false      : ∀{Γ} → Tm Γ Bool
      iteBool    : ∀{Γ A} → Tm Γ A → Tm Γ A → Tm Γ Bool → Tm Γ A
      Boolβ₁     : ∀{Γ A u v} → iteBool {Γ}{A} u v true ≡ u
      Boolβ₂     : ∀{Γ A u v} → iteBool {Γ}{A} u v false ≡ v
      true[]     : ∀{Γ Δ}{γ : Sub Δ Γ} → true [ γ ] ≡ true
      false[]    : ∀{Γ Δ}{γ : Sub Δ Γ} → false [ γ ] ≡ false
      iteBool[]  : ∀{Γ A t u v Δ}{γ : Sub Δ Γ} →
                   iteBool {Γ}{A} u v t [ γ ] ≡ iteBool (u [ γ ]) (v [ γ ]) (t [ γ ])

      Nat        : Ty
      zeroo      : ∀{Γ} → Tm Γ Nat
      suco       : ∀{Γ} → Tm Γ Nat → Tm Γ Nat
      iteNat     : ∀{Γ A} → Tm Γ A → Tm (Γ ▹ A) A → Tm Γ Nat → Tm Γ A
      Natβ₁      : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A} → iteNat u v zeroo ≡ u
      Natβ₂      : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A}{t : Tm Γ Nat} →
                   iteNat u v (suco t) ≡ v [ ⟨ iteNat u v t ⟩ ]
      zero[]     : ∀{Γ Δ}{γ : Sub Δ Γ} → zeroo [ γ ] ≡ zeroo
      suc[]      : ∀{Γ}{t : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} → (suco t) [ γ ] ≡ suco (t [ γ ])
      iteNat[]   : ∀{Γ A}{u : Tm Γ A}{v : Tm (Γ ▹ A) A}{t : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} →
                   iteNat u v t [ γ ] ≡ iteNat (u [ γ ]) (v [ γ ⁺ ]) (t [ γ ])
\end{code}
Coinductive types are dual to inductive types. Inductive types are
specified by their constructors, coinductive types are specified by
their destructors. Their constructor is determined by the destructors:
if we have a type \verb$C$ (the seed) together with terms which have
the shape of the destructors (but using \verb$C$ instead of the
coinductive type), we obtain a function (called corecursor, generator,
anamorphism) from the seed to the coinductive type. The seed is called
like that because the generator makes the coinductive type "grow" out
of it. While elements of inductive type are trees of finite depth,
elements of coinductive types are potentially infinitely deep
trees. Functions out of inductive types are all terminating, functions
producing elements of coinductive types are \emph{productive}.

The usual example is infinite lists or streams. There are two ways to
destruct a stream: look at its first element (head), or forget its
first element (tail). To generate a stream, we need to fix a seed type
\verb$C$ which represents the internal state of the stream; we have to
provide an \verb$A$ from any \verb$C$; we have to be able to step the
internal state when forgetting the first element; and finally, we need
a state to start with. The computation rules say what happens if a
destructor is applied to the constructor (generator): we use the
corresponding method with the actual internal state, and corecursively
call the generator on the new state, if needed.
\begin{code}
      Stream        : Ty → Ty
      head          : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ A
      tail          : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ (Stream A)
      genStream     : ∀{Γ A C} → Tm (Γ ▹ C) A → Tm (Γ ▹ C) C → Tm Γ C → Tm Γ (Stream A)
      Streamβ₁      : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C} →
                      head (genStream u v t) ≡ u [ ⟨ t ⟩ ]
      Streamβ₂      : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C} →
                      tail (genStream u v t) ≡ genStream u v (v [ ⟨ t ⟩ ])
      head[]        : ∀{Γ A}{as : Tm Γ (Stream A)}{Δ}{γ : Sub Δ Γ} →
                      head as [ γ ] ≡ head (as [ γ ])
      tail[]        : ∀{Γ A}{as : Tm Γ (Stream A)}{Δ}{γ : Sub Δ Γ} → tail as [ γ ] ≡ tail (as [ γ ])
      genStream[]   : ∀{Γ A C}{u : Tm (Γ ▹ C) A}{v : Tm (Γ ▹ C) C}{t : Tm Γ C}{Δ}
                      {γ : Sub Δ Γ} →
                      genStream u v t [ γ ] ≡ genStream (u [ γ ⁺ ]) (v [ γ ⁺ ]) (t [ γ ])
\end{code}
\verb$genStream$ binds a variable of type \verb$C$ in both its first end second explicit arguments.

State machines, virtual machines, Turing machines, servers, operating
systems are all coinductive types. An example simple machine has three
operations: (i) we can put in a natural number, (ii) we can press a button on it,
(iii) we can ask it to output a natural number.
\begin{code}
      Machine       : Ty
      put           : ∀{Γ} → Tm Γ Machine → Tm Γ Nat → Tm Γ Machine
      set           : ∀{Γ} → Tm Γ Machine → Tm Γ Machine
      get           : ∀{Γ} → Tm Γ Machine → Tm Γ Nat
      genMachine    : ∀{Γ C} → Tm (Γ ▹ C ▹ Nat) C → Tm (Γ ▹ C) C → Tm (Γ ▹ C) Nat →
                      Tm Γ C → Tm Γ Machine
      Machineβ₁     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                      {t : Tm Γ C}{t' : Tm Γ Nat} →
                      put (genMachine u v w t) t' ≡ genMachine u v w (u [ ⟨ t ⟩ ⁺ ] [ ⟨ t' ⟩ ])
      Machineβ₂     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                      {t : Tm Γ C} →
                      set (genMachine u v w t) ≡ genMachine u v w (v [ ⟨ t ⟩ ])
      Machineβ₃     : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                      {t : Tm Γ C} →
                      get (genMachine u v w t) ≡ w [ ⟨ t ⟩ ]
      put[]         : ∀{Γ}{t : Tm Γ Machine}{u : Tm Γ Nat}{Δ}{γ : Sub Δ Γ} →
                      put t u [ γ ] ≡ put (t [ γ ]) (u [ γ ])
      set[]         : ∀{Γ}{t : Tm Γ Machine}{Δ}{γ : Sub Δ Γ} → set t [ γ ] ≡ set (t [ γ ])
      get[]         : ∀{Γ}{t : Tm Γ Machine}{Δ}{γ : Sub Δ Γ} → get t [ γ ] ≡ get (t [ γ ])
      genMachine[]  : ∀{Γ C}{u : Tm (Γ ▹ C ▹ Nat) C}{v : Tm (Γ ▹ C) C}{w : Tm (Γ ▹ C) Nat}
                      {t : Tm Γ C}{Δ}{γ : Sub Δ Γ} →
                      genMachine u v w t [ γ ] ≡
                      genMachine (u [ γ ⁺ ⁺ ]) (v [ γ ⁺ ]) (w [ γ ⁺ ]) (t [ γ ])
\end{code}
\verb$genMachine$ binds a variable of type \verb$C$ and a variable of type \verb$Nat$ in its first explicit argument, and binds
a variable of type \verb$C$ in its second and third explicit arguments.
\begin{code}[hide]
module Examples where
  open import Coind.Syntax

  plus : ∀{Γ} → Tm Γ (Nat ⇒ Nat ⇒ Nat)
  plus = lam (lam (iteNat v0 (suco v0) v1))
\end{code}

The stream which contains the number \verb$0,1,2,...$:
\begin{code}
  numbers : Tm ◇ (Stream Nat)
  numbers = genStream v0 (suco v0) zeroo

  testNumbers0 : head numbers ≡ zeroo
  testNumbers0 =
    head numbers
      ≡⟨ refl {A = Tm _ _} ⟩
    head (genStream v0 (suco v0) zeroo)
      ≡⟨ Streamβ₁ ⟩
    v0 [ ⟨ zeroo ⟩ ]
      ≡⟨ vz[⟨⟩] ⟩
    zeroo
      ∎
\end{code}
\begin{exe}
Prove the following equation.
\textnormal{\begin{code}
  testNumbers2 : head (tail (tail numbers)) ≡ suco (suco zeroo)
\end{code}}
\begin{code}[hide]
  testNumbers2 = exercisep
\end{code}
\end{exe}
A machine which adds the numbers that we input unless we press the button, then it adds one when inputting a number. If we
toggle the button again, it will start adding the numbers again. The number it outputs is the current sum.
\begin{code}
  aMachine : Tm ◇ Machine
  aMachine = genMachine (fst v1 ,o (plus $ snd v1 $ v0))
    (iteBool false true (fst v0) ,o snd v0) (snd v0) (true ,o zeroo)
\end{code}

\begin{exe}[compulsory]
  For types \verb$A$, \verb$B$, define the coinductive type of machines from which we can get out
  an \verb$A$ and a \verb$B$. List all the rules. Derive these rules from those of binary products.
\end{exe}
\begin{exe}[compulsory]
  Given a language with machines as in the previous exercise, derive the rules of binary products!
  Which one is not derivable?
\end{exe}
\begin{exe}[compulsory]
  For types \verb$A$, \verb$B$, define the coinductive type of machines which has one operation:
  it receives an input of type \verb$A$, and outputs something of type \verb$B$. List all the rules.
  Derive these rules from those of the function space.
\end{exe}
\begin{exe}[compulsory]
  Given a language with machines as in the previous exercise, derive the rules of function space!
  Which one is not derivable?
\end{exe}
\begin{exe}[compulsory]
  Define the coinductive types of machines for which there are two different ways to input a natural number and if we press a button, they output a natural number.
  Implement a machine which has two numbers in its inner state and outputs one or the other alternating.
  If we input a number in the first way, the machine adds that to its first inner number. 
  If we input a number in the second way, the machine adds that to its second inner number. 
\end{exe}

\section{Standard model}

\begin{code}[hide]
module Standard where
\end{code}

We define streams and machines using Agda's coinductive types.
\begin{code}
  record Stream (A : Set) : Set where
    coinductive
    field
      head : A
      tail : Stream A
  open Stream
  genStream : {A C : Set} → (C → A) → (C → C) → C → Stream A
  head (genStream f g c) = f c
  tail (genStream f g c) = genStream f g (g c)

  record Machine : Set where
    coinductive
    field
      put : ℕ → Machine
      set : Machine
      get : ℕ
  open Machine
  genMachine : {C : Set} → (C → ℕ → C) → (C → C) → (C → ℕ) → C → Machine
  put (genMachine f g h c) n = genMachine f g h (f c n)
  set (genMachine f g h c) = genMachine f g h (g c)
  get (genMachine f g h c) = h c
\end{code}

\begin{code}[hide]
  open import Coind.Model
  
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

    ; _×o_      = _×_
    ; _,o_      = λ a b γ → a γ , b γ
    ; fst       = λ ab γ → π₁ (ab γ)
    ; snd       = λ ab γ → π₂ (ab γ)
    ; ×β₁       = refl
    ; ×β₂       = refl
    ; ×η        = refl
    ; ,[]       = refl
  
    ; Bool      = 𝟚
    ; true      = λ _ → tt
    ; false     = λ _ → ff
    ; iteBool   = λ u v t γ* → if t γ* then u γ* else v γ*
    ; Boolβ₁    = refl
    ; Boolβ₂    = refl
    ; true[]    = refl
    ; false[]   = refl
    ; iteBool[] = refl
    
    ; Nat        = ℕ
    ; zeroo      = λ _ → zero
    ; suco       = λ t γ* → suc (t γ*)
    ; iteNat     = λ u v t γ* → iteℕ (u γ*) (λ x → v (γ* , x)) (t γ*)
    ; Natβ₁      = refl
    ; Natβ₂      = refl
    ; zero[]     = refl
    ; suc[]      = refl
    ; iteNat[]   = refl
\end{code}

The new components in the standard model:
\begin{code}
    ; Stream        = Stream
    ; head          = λ t γ* → head (t γ*)
    ; tail          = λ t γ* → tail (t γ*)
    ; genStream     = λ u v t γ* → genStream (λ x → u (γ* , x)) (λ x → v (γ* , x)) (t γ*)
    ; Streamβ₁      = refl
    ; Streamβ₂      = refl
    ; head[]        = refl
    ; tail[]        = refl
    ; genStream[]   = refl

    ; Machine       = Machine
    ; put           = λ t u γ* → put (t γ*) (u γ*) 
    ; set           = λ t γ* → set (t γ*)
    ; get           = λ t γ* → get (t γ*)
    ; genMachine    = λ u v w t γ* → genMachine (λ x y → u ((γ* , x) , y))
                      (λ x → v (γ* , x)) (λ x → w (γ* , x)) (t γ*)
    ; Machineβ₁     = refl
    ; Machineβ₂     = refl
    ; Machineβ₃     = refl
    ; put[]         = refl
    ; set[]         = refl
    ; get[]         = refl
    ; genMachine[]  = refl
\end{code}
\begin{code}[hide]
    }
\end{code}
