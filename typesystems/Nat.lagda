\subsection{Another example of iteration and induction: natural numbers}
\label{sec:natural}

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module Nat where
open import Lib
\end{code}
A model of naturals is a set \verb$Nat$ with an element \verb$Zero$ and an endofunction \verb$Suc$.
\begin{code}
record Model {ℓ} : Set (lsuc ℓ) where
  field
    Nat   : Set ℓ
    Zero  : Nat
    Suc   : Nat → Nat
\end{code}
\begin{code}[hide]
  ⟦_⟧ : ℕ → Nat
  ⟦ zero ⟧ = Zero
  ⟦ suc n ⟧ = Suc ⟦ n ⟧
\end{code}
There is a model \verb$I$ given by actual natural numbers.
\begin{code}
I : Model
I = record { Nat = ℕ ; Zero = 0 ; Suc = 1 +_ }
\end{code}
\begin{code}[hide]
module I = Model I
\end{code}
For any other model \verb$M$, we have a function from \verb$I.Nat$ to \verb$M.Nat$ which respects the two operations.
\begin{verbatim}
M.⟦_⟧ : I.Nat → M.Nat
M.⟦ I.Zero ⟧ = M.Zero
M.⟦ I.Suc n ⟧ = M.Suc M.⟦ n ⟧
\end{verbatim}
We define the following model where \verb$Nat$ is syntactic natural numbers.
\begin{code}
M : Model
M = record { Nat = I.Nat ; Zero = I.Suc I.Zero ; Suc = λ n → I.Suc (I.Suc n) }
\end{code}
\begin{code}[hide]
module M = Model M
\end{code}
Interpretation into \verb$M$ is the function $n \mapsto 2*n+1$:
\begin{code}
testM0 : M.⟦ 0 ⟧  ≡ 1
testM1 : M.⟦ 1 ⟧  ≡ 3
testM2 : M.⟦ 2 ⟧  ≡ 5
\end{code}
\begin{code}[hide]
testM0 = refl
testM1 = refl
testM2 = refl
\end{code}
Now we define a model where \verb$Nat$ is endofunctions on \verb$I.Nat$, \verb$Zero$ is the identity function, and \verb$Suc$ is post-composition with \verb$I.Suc$.
\begin{code}
A : Model
A = record { Nat = I.Nat → I.Nat ; Zero = λ n → n ; Suc = λ f → I.Suc ∘ f }
\end{code}
\begin{code}[hide]
module A = Model A
\end{code}
Interpretation into \verb$A$ is the function that maps $n$ into the function which adds $n$ to a number:
\begin{code}
testA0 : A.⟦ 0 ⟧  ≡ λ n → n
testA1 : A.⟦ 1 ⟧  ≡ I.Suc
testA2 : A.⟦ 2 ⟧  ≡ I.Suc ∘ I.Suc
testA3 : A.⟦ 3 ⟧  ≡ I.Suc ∘ I.Suc ∘ I.Suc
\end{code}
\begin{code}[hide]
testA0 = refl
testA1 = refl
testA2 = refl
testA3 = refl
\end{code}
Thus we can define addition of natural numbers as follows.
\begin{code}
_+'_ : I.Nat → I.Nat → I.Nat
_+'_ = A.⟦_⟧
\end{code}
\begin{code}
test1+3 : 1 +' 3 ≡ 4
test3+2 : 3 +' 2 ≡ 5
\end{code}
\begin{code}[hide]
test1+3 = refl
test3+2 = refl
\end{code}
A dependent model is the data for induction on natural numbers (we use only \verb$Prop$-valued families for convenience, so this is not the mose general version of \verb$DepModel$).
\begin{code}
record DepModel {ℓ} : Set (lsuc ℓ) where
  field
    Nat∙   : I.Nat → Prop ℓ
    Zero∙  : Nat∙ I.Zero
    Suc∙   : {n : I.Nat} → Nat∙ n → Nat∙ (I.Suc n)
\end{code}
\begin{code}[hide]
  ⟦_⟧ : (n : I.Nat) → Nat∙ n
  ⟦ zero ⟧ = Zero∙
  ⟦ suc n ⟧ = Suc∙ ⟦ n ⟧
\end{code}
For example, we prove associativity of the above addition by the following dependent model.
The \verb$Nat$ component says what we want to prove for each number, the \verb$Zero$ component is the base case, the \verb$Suc$ components is the inductive case.
\begin{code}
Ass : (n o : I.Nat) → DepModel
Ass n o = record
  {  Nat∙   = λ m → (m +' n) +' o ≡ m +' (n +' o)
  ;  Zero∙  = refl
  ;  Suc∙   = cong suc
  }
\end{code}
The base case holds by reflexivity, in the inductive case we simply use the induction hypothesis. Now we obtain
the proof of associativity by interpreting into the dependent model \verb$Ass$.
\begin{code}
ass : (m n o : I.Nat) → (m +' n) +' o ≡ m +' (n +' o)
ass m n o = Assno.⟦_⟧ m
  where
    module Assno = DepModel (Ass n o)
\end{code}
\begin{exe}[recommended]
Show that \verb$0$ is right unit for addition using another dependent model.
\end{exe}
\begin{code}
Identityʳ : DepModel
Identityʳ = record
  { Nat∙ = λ x → x +' I.Zero ≡ x
  ; Zero∙ = refl
  ; Suc∙ = cong suc
  }

identityʳ : (x : I.Nat) → (x +' I.Zero ≡ x)
identityʳ = Identityʳ.⟦_⟧
  where
    module Identityʳ = DepModel Identityʳ
\end{code}
\begin{exe}[recommended]
Show that \verb$+$ is commutative. You will need two separate dependent models.
\end{exe}
\begin{code}

+Suc' : (y : I.Nat) → DepModel
+Suc' y = record
  { Nat∙ = λ x → x +' (I.Suc y) ≡ I.Suc (x +' y)
  ; Zero∙ = refl
  ; Suc∙ = cong suc
  }

+suc' : (x y : I.Nat) → x +' (suc y) ≡ suc (x +' y)
+suc' x y = +Suc'.⟦ x ⟧
  where
    module +Suc' = DepModel (+Suc' y)


Comm : (y : I.Nat) → DepModel
Comm y = record
  { Nat∙ = λ x → x +' y ≡ y +' x
  ; Zero∙ = identityʳ (I.Zero +' y) ⁻¹
  ; Suc∙ = λ {x} p → cong suc p ◾ +suc' y x ⁻¹
  }

comm : (x y : I.Nat) → x +' y ≡ y +' x
comm x y = Comm.⟦ x ⟧
  where
    module Comm = DepModel (Comm y)
\end{code}
\begin{exe}[recommended]
Show that the operators of the syntax are disjoint: \verb$I.Suc i ≠ I.Zero$.
\end{exe}
\begin{code}
suc≠zero' : ∀ {i} → ¬ (I.Suc i ≡ I.Zero)
suc≠zero' = λ ()
\end{code}
\begin{exe}[recommended]
Show that \verb$I.Suc$ is injective.
\end{exe}
