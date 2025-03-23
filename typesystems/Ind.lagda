\chapter{Inductive types}
\label{ch:Ind}

\begin{tcolorbox}[title=Learning goals of this chapter]
  Inductive types by examples: natural numbers, unit, lists, binary trees.
  Type formers, constructors, iterator, recursor, defining functions by iteration.
  Inductive types don't have \verb$η$ rules.
  Definability, examples of definable and non definable functions.
\end{tcolorbox}

TODO: example: syntax as an inductive type.

TODO: add mutual inductive types, e.g. Odd and Even.

\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
open import Lib

module Ind where

module tmp where
  record Model {i j} : Set (lsuc (i ⊔ j)) where
    infixl 6 _[_]
    infixl 5 _▹_
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

      _⇒_    : Ty → Ty → Ty
      lam    : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
      _$_    : ∀{Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
      ⇒β     : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A} → lam t $ u ≡ t [ ⟨ u ⟩ ]
      ⇒η     : ∀{Γ A B}{t : Tm Γ (A ⇒ B)} → t ≡ lam (t [ p ] $ var vz)
      lam[]  : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{Δ}{σ : Sub Δ Γ} → lam t [ σ ] ≡ lam (t [ σ ⁺ ])
      $[]    : ∀{Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A}{Δ}{σ : Sub Δ Γ} →
               (t $ u) [ σ ] ≡ (t [ σ ]) $ (u [ σ ])

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
\end{code}

An inductive type is specified by its constructors. Its destructor and
computation rules are determined by the constructors: the destructor
says that for any type \verb$C$ (called motive) and elements of that
type which have the shape of the constructors (these are called
methods), there is a function (called iterator, fold,
catamorphism) from the inductive type to \verb$C$. The computation
rules say that if we apply the iterator to a constructor, we obtain
the corresponding method.

We have already seen some inductive types: \verb$Bool$ had two
constructors \verb$true$ and \verb$false$, and its iterator was called
if-then-else, it said that for any type \verb$C$ and two elements of
\verb$C$, there is a function from \verb$Bool$ to \verb$C$. For any
two types \verb$A$ and \verb$B$, the sum \verb$A +o B$ was an
inductive type with constructors \verb$inl$ and \verb$inr$. Its
iterator was called \verb$caseo$, it said that for any type \verb$C$
and elements \verb$A → C$ and \verb$B → C$, there is a function from
\verb$A +o B$ to \verb$C$. In fact, sums also came with an \verb$η$
rule which is not usual for inductive types.

Natural numbers are also an inductive type: the constructors are
\verb$zero$ and \verb$suc$, the latter can be written in several
different equivalent ways:
\begin{verbatim}
suc : Tm Γ Nat → Tm Γ Nat
suc : Tm Γ (Nat ⇒ Nat)
suc : Tm (Γ ▹ Nat) Nat
\end{verbatim}
When specifying the arguments of the iterator, we use the last version
which does not refer to metatheoretic or object theoretic function space.
So the iterator says that given a type \verb$C$, a term in \verb$Tm Γ C$
and a term in \verb$Tm (Γ ▹ C) C$, we get a function from \verb$Tm Γ Nat$ to
\verb$Tm Γ C$.

A language has natural numbers if it extends the substitution calculus
with the following operators and equations:
\begin{code}
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
\verb$iteNat$ binds a variable of type \verb$A$ in its second argument.
The computation rules \verb$Natβ₁$ and \verb$Natβ₂$ express that
\verb$iteNat u v t$ works as follows: it replaces all \verb$suco$s in
\verb$t$ by what is specified by \verb$v$, and replaces \verb$zeroo$ by
\verb$u$. For example, \verb$iteNat u v (suco (suco (suco zero)))$ is
equal to \verb$v [ ⟨ v [ ⟨ v [ ⟨ u ⟩ ] ⟩ ] ⟩ ]$ (which can be thought about as
\verb$v (v (v u))$ but we use substitution to express the applications).

Gödel's System T is the name of the language which has function space
\verb$⇒$ and natural numbers as above.

The simplest inductive type is that with only one constructor \verb$trivial$. Note that this
is not the same as the \verb$Unit$ type in the previous chapter, where it had an \verb$η$ rule.
\begin{code}
      Unit       : Ty
      trivial    : ∀{Γ} → Tm Γ Unit
      iteUnit    : ∀{Γ A} → Tm Γ A → Tm Γ Unit → Tm Γ A
      Unitβ      : ∀{Γ A t} → iteUnit {Γ}{A} t trivial ≡ t
      trivial[]  : ∀{Γ Δ}{γ : Sub Δ Γ} → trivial [ γ ] ≡ trivial
      iteUnit[]  : ∀{Γ A t u Δ}{γ : Sub Δ Γ} →
                   iteUnit {Γ}{A} u t [ γ ] ≡ iteUnit (u [ γ ]) (t [ γ ])
\end{code}

Another inductive type is that of lists. For any type \verb$A$, we have a
type \verb$List A$. It has two constructors \verb$nil : Tm Γ (List A)$ and
\verb$cons$ which again can be expressed in three different ways. We will use
the first one when specifying the constructor and the third one when specifying
the arguments of the iterator.
\begin{verbatim}
cons : Tm Γ A → Tm Γ (List A) → Tm Γ (List A)
cons : Tm Γ (A ⇒ List A ⇒ List A)
cons : Tm (Γ ▹ A ▹ List A) (List A)
\end{verbatim}
A language has lists if it extends the substitution calculus with the following
operators and equations:
\begin{code}
      List       : Ty → Ty
      nil        : ∀{Γ A} → Tm Γ (List A)
      cons       : ∀{Γ A} → Tm Γ A → Tm Γ (List A) → Tm Γ (List A)
      iteList    : ∀{Γ A B} → Tm Γ B → Tm (Γ ▹ A ▹ B) B → Tm Γ (List A) → Tm Γ B
      Listβ₁     : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B} → iteList u v nil ≡ u
      Listβ₂     : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B}{t₁ : Tm Γ A}{t : Tm Γ (List A)} →
                   iteList u v (cons t₁ t) ≡ (v [ ⟨ t₁ ⟩ ⁺ ] [ ⟨ iteList u v t ⟩ ])
      nil[]      : ∀{Γ A Δ}{γ : Sub Δ Γ} → nil {Γ}{A} [ γ ] ≡ nil {Δ}{A}
      cons[]     : ∀{Γ A}{t₁ : Tm Γ A}{t : Tm Γ (List A)}{Δ}{γ : Sub Δ Γ} →
                   (cons t₁ t) [ γ ] ≡ cons (t₁ [ γ ]) (t [ γ ])
      iteList[]  : ∀{Γ A B}{u : Tm Γ B}{v : Tm (Γ ▹ A ▹ B) B}{t : Tm Γ (List A)}{Δ}{γ : Sub Δ Γ} →
                   iteList u v t [ γ ] ≡ iteList (u [ γ ]) (v [ γ ⁺ ⁺  ]) (t [ γ ])
\end{code}
\verb$iteList$ binds a variable of type \verb$A$ and another variable of type \verb$B$ in its second explicit argument. In \verb$iteList u v t$, \verb$u$ expresses what to do when \verb$t = nil t'$, \verb$v$ expresses what to do when \verb$t = cons t' t''$.

Another inductive type is that of binary trees with information at the
leaves. For any type \verb$A$, \verb$Ty A$ is a type, the constructors are
\verb$leaf$ and \verb$node$. A language has these binary trees if it has the
following operators and equations:
\begin{code}
      Tree       : Ty → Ty
      leaf       : ∀{Γ A} → Tm Γ A → Tm Γ (Tree A)
      node       : ∀{Γ A} → Tm Γ (Tree A) → Tm Γ (Tree A) → Tm Γ (Tree A)
      iteTree    : ∀{Γ A B} → Tm (Γ ▹ A) B → Tm (Γ ▹ B ▹ B) B → Tm Γ (Tree A) → Tm Γ B
      Treeβ₁     : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{a : Tm Γ A} →
                   iteTree l n (leaf a) ≡ l [ ⟨ a ⟩ ]
      Treeβ₂     : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{ll rr : Tm Γ (Tree A)} →
                   iteTree l n (node ll rr) ≡ n [ ⟨ iteTree l n ll ⟩ ⁺ ] [ ⟨ iteTree l n rr ⟩ ]
      leaf[]     : ∀{Γ A}{a : Tm Γ A}{Δ}{γ : Sub Δ Γ} → (leaf a) [ γ ] ≡ leaf (a [ γ ])
      node[]     : ∀{Γ A}{ll rr : Tm Γ (Tree A)}{Δ}{γ : Sub Δ Γ} →
                   (node ll rr) [ γ ] ≡ node (ll [ γ ]) (rr [ γ ])
      iteTree[]  : ∀{Γ A B}{l : Tm (Γ ▹ A) B}{n : Tm (Γ ▹ B ▹ B) B}{t : Tm Γ (Tree A)}
                   {Δ}{γ : Sub Δ Γ} →
                   iteTree l n t [ γ ] ≡ iteTree (l [ γ ⁺ ]) (n [ γ ⁺ ⁺ ]) (t [ γ ])
\end{code}
\verb$iteTree$ binds a variable of type \verb$A$ in its first explicit argument and two variables of type \verb$B$ in its second explicit argument.

\begin{code}[hide]
module Examples where
  open import Ind.Syntax
\end{code}

The functions defined by iterators are all terminating. Even though
they are recursive functions, infinite recursion is not possible,
because the target of the iteration decreases at each recursive call.

The recursor (primitive recursor, paramorphism \cite{DBLP:conf/mpc/YangW22}) for natural numbers does not only
receive the result of the recursive call, but also the number.
\begin{code}
  recNat     : ∀{Γ A} → Tm Γ A → Tm (Γ ▹ Nat ▹ A) A → Tm Γ Nat → Tm Γ A
  recNatβ₁   : ∀{Γ A u v} → recNat {Γ}{A} u v zeroo ≡ u
  ¬recNatβ₂  : ¬ (∀{Γ A u v t} → recNat {Γ}{A} u v (suco t) ≡ v [ ⟨ t ⟩ ⁺ ] [ ⟨ recNat u v t ⟩ ])
\end{code}
For example, with the iterator, it is not possible to define a function \verb$pred : Tm (◇ ▹ Nat) Nat$ s.t.\ \verb$pred [ ⟨ suco t ⟩ ] ≡ t$ for any \verb$t$ (note that \verb$t$ might be a variable e.g.\ \verb$q$) \cite{DBLP:conf/csl/Parigot89}.
\begin{exe}[recommended]
Define the recursor for natural numbers with the help of the iterator and show that it satisfies \verb$recNatβ₁$.
\begin{code}[hide]
  recNat = exercise
  recNatβ₁ = exercisep
\end{code}
\end{exe}
\begin{exe}[very hard]
Show that \verb$recNatβ₂$ does not hold in the syntax (you need a countermodel).
\begin{code}[hide]
  ¬recNatβ₂ = exercisep
\end{code}
\end{exe}

The iterator is like a for loop where the body of the loop cannot refer to the loop variable. Recursor is like a general for loop.
A fixpoint combinator is like while loop. A fixpoint combinator is defined by the following operator and equations:
\begin{verbatim}
fix    : Tm (Γ ▹ A) A → Tm Γ A
fixβ   : fix t ≡ t [ ⟨ fix t ⟩ ]
fix[]  : fix t [ γ ] ≡ fix (t [ γ ⁺ ])
\end{verbatim}

In the case of \verb$Bool$ (or other non-recursive inductive types),
there is no difference between the iterator and the recursor.

Our previous definition of \verb$Nat$ (in Section \ref{sec:def})
was not an inductive type because it did not have an iterator or
recursor, only two special cases of the iterator: addition and
\verb$isZero$. Both of these can be defined using the iterator.

With the iterator, we can define the following functions on natural
numbers. Addition with variable names is written
\verb$plus = λ x y . iteNat y (z . suc z) x$
which means that we have a function with two inputs \verb$x$ and \verb$y$,
we do recursion on the first input (\verb$x$), and in the input, we replace
\verb$zero$s by \verb$y$, and \verb$suc$s by \verb$suc$. The same information
is expressed in languages with pattern matching as follows.
\begin{verbatim}
plus zero      y = y
plus (suc x') y = suc (plus x' y)
\end{verbatim}
The first line corresponds to the first argument of \verb$iteNat$ (i.e.\ \verb$y$),
the second line corresponds to the second argument in which \verb$z$ is bound
(\verb$z . suc z$) where \verb$z$ refers to the recursive call which we
write \verb$(plus x' y)$ using pattern matching notation.

In our formal
syntax, we write this as follows.
\begin{code}
  plus : Tm ◇ (Nat ⇒ Nat ⇒ Nat)
  plus = lam (lam (iteNat v0 (suco v0) v1))
\end{code}
The \verb$isZero$ operation can be defined as follows.
\begin{code}
  isZero : Tm ◇ (Nat ⇒ Bool)
  isZero = lam (iteNat true false v0)
\end{code}
The zero case is simply \verb$true$, the successor case is \verb$false$
regardless of the result of the recursive call.

\begin{exe}[compulsory]
Define \verb$num$ as syntactic sugar, and show that \verb$plus$ and \verb$isZero$ satisfy the same
computation rules as in Razor!
\textnormal{\begin{code}
  num : ∀{Γ} → ℕ → Tm Γ Nat
  plusβ : ∀{n m} → plus $ num n $ num m ≡ num (n + m)
  isZeroβ₁ : isZero $ num 0 ≡ true
  isZeroβ₂ : ∀{n} → isZero $ num (1 + n) ≡ false
\end{code}}
\begin{code}[hide]
  num = exercise
  plusβ = exercisep
  isZeroβ₁ = exercisep
  isZeroβ₂ = exercisep
\end{code}
\end{exe}

Examples function definitions for lists:
\begin{code}
  isnil : {A : Ty} → Tm ◇ (List A ⇒ Bool)
  isnil = lam (iteList true false v0)

  concat : {A : Ty} → Tm ◇ (List A ⇒ List A ⇒ List A)
  concat = lam (lam (iteList v0 (cons v1 v0) v1))
\end{code}
\verb$isnil$ and \verb$concat$ are polymorphic functions in the sense
that they work for any type \verb$A$ but the polymorphism happens in
our metalanguage and not in our object language.

The following two trees in \verb$Tm ◇ (Tree Nat)$

\begin{tikzpicture}
  \node (x10) at (0,0) {};
  \node (x20) at (-0.5,-1) {};
  \node (x21) at (0.5,-1) {\verb$zero$};
  \node (x30) at (-1,-2) {\verb$zero$};
  \node (x31) at (0,-2) {\verb$zero$};
  \draw[-] (x10) edge node {} (x20);
  \draw[-] (x10) edge node {} (x21);
  \draw[-] (x20) edge node {} (x30);
  \draw[-] (x20) edge node {} (x31);
  \node (y10) at (3,0) {};
  \node (y20) at (2.5,-1) {\verb$zero$};
  \node (y21) at (3.5,-1) {};
  \node (y30) at (3,-2) {\verb$zero$};
  \node (y31) at (4,-2) {\verb$zero$};
  \draw[-] (y10) edge node {} (y20);
  \draw[-] (y10) edge node {} (y21);
  \draw[-] (y21) edge node {} (y30);
  \draw[-] (y21) edge node {} (y31);
\end{tikzpicture}

are defined as
\begin{code}[hide]
  treeEx1 treeEx2 : Tm ◇ (Tree Nat)
\end{code}
\begin{code}
  treeEx1 = node (node (leaf zeroo) (leaf zeroo)) (leaf zeroo)
  treeEx2 = node (leaf zeroo) (node (leaf zeroo) (leaf zeroo))
\end{code}

The following function adds all the numbers in the leaves of a tree.
\begin{code}
  sum : Tm ◇ (Tree Nat ⇒ Nat)
  sum = lam (iteTree v0 (plus [ p ] [ p ] [ p ] $ v1 $ v0) v0)
\end{code}
With variable names, we would write this as
\verb@sum = λ x . iteTree (z . z) (z₁ z₂ . plus $ z₁ $ z₂) x@.
In the formal syntax, we had to weaken \verb$plus$ three times by \verb$_[ p ]$
because it was defined in the empty context above and now we used it
in a context with three free variables (one bound by \verb$lam$, the other
two by \verb$iteTree$).

The following function turns a binary tree into a list:
\begin{code}
  flatten : ∀{A} → Tm ◇ (Tree A ⇒ List A)
  flatten = lam (iteTree (cons v0 nil) (concat [ p ] [ p ] [ p ] $ v1 $ v0) v0)
\end{code}

\begin{exe}[compulsory]
  List the rules for inductively defined trees with ternary branching, a boolean at each node and a natural number at each leaf.
\end{exe}
\begin{exe}[compulsory]
  List the rules for inductively defined trees with two kinds of nullary, one kind of binary and three kinds of ternary branching. There is no extra information at leaves or nodes.
\end{exe}
\begin{exe}[compulsory]
  List the rules for inductively defined trees no information at the leaves and infinity (\verb$Nat$-ary) branching.
\end{exe}
\begin{exe}[compulsory]
  For types \verb$A$, \verb$B$, list the rules for the inductive type with only leaves (and no nodes) that contain an \verb$A$ and a \verb$B$. Derive all its rules from binary products of the previous section. Which rule of binary products cannot be derived from this inductive type?
\end{exe}
\begin{exe}[compulsory]
  For types \verb$A$, \verb$B$, list the rules for the inductive type with two kinds of leaves and no nodes. One kind of leaf contains an \verb$A$, the other kind of leaf contains a \verb$B$. Derive all the rules from binary sums of the previous section. Which rule of binary sums cannot be derived from this inductive type?
\end{exe}
\begin{exe}[compulsory]
  How many elements are in the inductive type with only the following constructors?
  \begin{verbatim}
  SpecialTree : Ty
  node1 : Tm Γ SpecialTree → Tm Γ SpecialTree
  node2 : Tm Γ SpecialTree → Tm Γ SpecialTree → Tm Γ SpecialTree
  \end{verbatim}
\end{exe}

\section{No uniqueness rules}

Inductive types usually don't come with \verb$η$ rules. If natural
numbers had an \verb$η$ rule, that would make equality
undecidable. Because there is no \verb$η$, we have many, non-equal
implementations of the same function. For example, we list some
implementations of the identity function on natural numbers.
And there are infinitely many more.
\begin{code}
  id id' id'' : ∀{Γ} → Tm Γ (Nat ⇒ Nat)
  id    = lam (var vz)
  id'   = lam (iteNat zeroo (suco v0) v0)
  id''  = lam (iteNat v0 v0 v0)
\end{code}
We can show that these are not equal using normalisation.

Similarly, there are infinitely many boolean negation functions.
\begin{exe}
Write down infinitely many different terms in $Tm ◇ (Bool ⇒ Bool)$!
\end{exe}

\begin{exe}
How many terms are in $Tm ◇ (Unit ⇒ Unit)$ where \verb$Unit$ is the inductively defined unit type without \verb$η$?
\end{exe}

\begin{exe}
Show that for each of the above inductive types, we can define a model where there are nonstandard elements of the inductive types.
\end{exe}

\section{Standard model}

\begin{code}[hide]
module Standard where
\end{code}

We define lists and trees using Agda's inductive types.
\begin{code}
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A
  infixr 5 _∷_
  iteList : {A B : Set} → B → (A → B → B) → List A → B
  iteList b f [] = b
  iteList b f (a ∷ as) = f a (iteList b f as)

  data Tree (A : Set) : Set where
    leaf : A → Tree A
    node : Tree A → Tree A → Tree A
  iteTree : {A B : Set} → (A → B) → (B → B → B) → Tree A → B
  iteTree f g (leaf a) = f a
  iteTree f g (node t t') = g (iteTree f g t) (iteTree f g t')
\end{code}

\begin{code}[hide]
  open import Ind.Model

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

    ; Bool      = 𝟚
    ; true      = λ _ → tt
    ; false     = λ _ → ff
    ; iteBool   = λ u v t γ* → if t γ* then u γ* else v γ*
    ; Boolβ₁    = refl
    ; Boolβ₂    = refl
    ; true[]    = refl
    ; false[]   = refl
    ; iteBool[] = refl
  \end{code}

  The new components in the standard model:
  \begin{code}
    ; Nat        = ℕ
    ; zeroo      = λ _ → zero
    ; suco       = λ t γ* → suc (t γ*)
    ; iteNat     = λ u v t γ* → iteℕ (u γ*) (λ x → v (γ* , x)) (t γ*)
    ; Natβ₁      = refl
    ; Natβ₂      = refl
    ; zero[]     = refl
    ; suc[]      = refl
    ; iteNat[]   = refl

    ; Unit      = Lift ⊤
    ; trivial   = λ _ → mk triv
    ; iteUnit   = λ z _ → z
    ; Unitβ     = refl
    ; trivial[] = refl
    ; iteUnit[] = refl

    ; List       = List
    ; nil        = λ _ → []
    ; cons       = λ u v γ* → u γ* ∷ v γ*
    ; iteList    = λ u v t γ* → iteList (u γ*) (λ x y → v ((γ* , x) , y)) (t γ*)
    ; Listβ₁     = refl
    ; Listβ₂     = refl
    ; nil[]      = refl
    ; cons[]     = refl
    ; iteList[]  = refl

    ; Tree       = Tree
    ; leaf       = λ t γ* → leaf (t γ*)
    ; node       = λ u v γ* → node (u γ*) (v γ*)
    ; iteTree    = λ {Γ}{A}{B} u v t γ* → iteTree (λ x → u (γ* , x)) (λ x y → v ((γ* , x) , y)) (t γ*)
    ; Treeβ₁     = refl
    ; Treeβ₂     = refl
    ; leaf[]     = refl
    ; node[]     = refl
    ; iteTree[]  = refl
\end{code}
\begin{code}[hide]
    }
  module St = Model St

  open import Ind.Syntax
\end{code}

\begin{code}
  t≠suct : ∀{t} → ¬ (t ≡ suco {◇} t)
  t≠suct {t} e = n≠sucn (cong (λ z → St.⟦ z ⟧t (mk triv)) e)
    where
      n≠sucn : {n : ℕ} → ¬ (n ≡ suc n)
      n≠sucn ()
\end{code}

\section{Definable functions on natural numbers}

The Ackermann function is not definable using first-order primitive
recursion (that is, in Def + natural numbers as a \verb$Tm (◇ ▹ Nat) Nat$).
But it is definable in our language because we have
higher-order functions \cite[Section 9.3]{harper}. Here is its definition in
Agda:
\begin{code}
ack : (x y : ℕ) -> ℕ
ack zero n = 1 + n
ack (suc m) zero = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)
\end{code}

\begin{code}[hide]
module Definability where
  open import Ind.Syntax
\end{code}
Natural numbers are included in terms.
\begin{code}
  ⌜_⌝ : ℕ → Tm ◇ Nat
  ⌜ zero ⌝ = zeroo
  ⌜ suc n ⌝ = suco ⌜ n ⌝
\end{code}
A function on natural numbers is definable if there is a term that, when applied to a natural
number, gives the same result as the function.
\begin{code}
  Definable : (ℕ → ℕ) → Set
  Definable f = Σsp (Tm ◇ (Nat ⇒ Nat)) λ t → (n : ℕ) → t $ ⌜ n ⌝ ≡ ⌜ f n ⌝
\end{code}
For example, the times two function is definable.
\begin{code}
  definable2* : Definable (iteℕ zero (λ x → suc (suc x)))
  definable2* = (lam (iteNat zeroo (suco (suco v0)) v0)) , λ n → 
    lam (iteNat zeroo (suco (suco v0)) v0) $ ⌜ n ⌝
        ≡⟨ ⇒β ⟩
    iteNat zeroo (suco (suco v0)) v0 [ ⟨ ⌜ n ⌝ ⟩ ]
        ≡⟨ iteNat[] ⟩
    iteNat (zeroo [ ⟨ ⌜ n ⌝ ⟩ ]) (suco (suco v0) [ ⟨ ⌜ n ⌝ ⟩ ⁺ ]) (v0 [ ⟨ ⌜ n ⌝ ⟩ ])
        ≡⟨ cong (λ x → iteNat x (suco (suco v0) [ ⟨ ⌜ n ⌝ ⟩ ⁺ ]) (v0 [ ⟨ ⌜ n ⌝ ⟩ ])) zero[] ⟩
    iteNat zeroo (suco (suco v0) [ ⟨ ⌜ n ⌝ ⟩ ⁺ ]) (v0 [ ⟨ ⌜ n ⌝ ⟩ ])
        ≡⟨ cong (λ x → iteNat zeroo x (v0 [ ⟨ ⌜ n ⌝ ⟩ ])) suc[] ⟩
    iteNat zeroo (suco (suco v0 [ ⟨ ⌜ n ⌝ ⟩ ⁺ ])) (v0 [ ⟨ ⌜ n ⌝ ⟩ ])
        ≡⟨ cong (λ x → iteNat zeroo (suco x) (v0 [ ⟨ ⌜ n ⌝ ⟩ ])) suc[] ⟩
    iteNat zeroo (suco (suco (v0 [ ⟨ ⌜ n ⌝ ⟩ ⁺ ]))) (v0 [ ⟨ ⌜ n ⌝ ⟩ ])
        ≡⟨ cong (λ x → iteNat zeroo (suco (suco x)) (v0 [ ⟨ ⌜ n ⌝ ⟩ ])) vz[⁺] ⟩
    iteNat zeroo (suco (suco v0)) (v0 [ ⟨ ⌜ n ⌝ ⟩ ])
        ≡⟨ cong (iteNat zeroo (suco (suco v0))) vz[⟨⟩] ⟩
    iteNat zeroo (suco (suco v0)) ⌜ n ⌝
        ≡⟨ ⌜rec⌝ n ⁻¹ ⟩
      ⌜ iteℕ zero (λ x → suc (suc x)) n ⌝
        ∎
    where
      ⌜rec⌝ : (n : ℕ) → ⌜ iteℕ zero (λ x → suc (suc x)) n ⌝ ≡ iteNat zeroo (suco (suco v0)) ⌜ n ⌝
      ⌜rec⌝ zero = Natβ₁ ⁻¹
      ⌜rec⌝ (suc n) =
        suco (suco ⌜ iteℕ zero (λ x → suc (suc x)) n ⌝)
          ≡⟨ cong {A = Tm _ _}(λ x → suco (suco x)) (⌜rec⌝ n) ⟩
        suco (suco (iteNat zeroo (suco (suco v0)) ⌜ n ⌝))
          ≡⟨ cong {A = Tm _ _}(λ x → suco (suco x)) (vz[⟨⟩] ⁻¹) ⟩
        suco (suco (v0 [ ⟨ iteNat zeroo (suco (suco v0)) ⌜ n ⌝ ⟩ ]))
          ≡⟨ cong suco (suc[] ⁻¹) ⟩
        suco (suco v0 [ ⟨ iteNat zeroo (suco (suco v0)) ⌜ n ⌝ ⟩ ])
          ≡⟨ suc[] ⁻¹ ⟩
        suco (suco v0) [ ⟨ iteNat zeroo (suco (suco v0)) ⌜ n ⌝ ⟩ ]
          ≡⟨ Natβ₂ ⁻¹ ⟩
        iteNat zeroo (suco (suco v0)) (suco ⌜ n ⌝)
          ∎
\end{code}
Here is definability for two-argument functions.
\begin{code}
  Definable' : (ℕ → ℕ → ℕ) → Set
  Definable' f = Σ (Tm ◇ (Nat ⇒ Nat ⇒ Nat)) λ t → (m n : ℕ) → Lift (t $ ⌜ m ⌝ $ ⌜ n ⌝ ≡ ⌜ f m n ⌝)
\end{code}
It is (relatively) easy to encode terms as natural numbers, for now we only assume a
\verb$code$ function.
\begin{code}
  postulate
    code : Tm ◇ (Nat ⇒ Nat) → ℕ
\end{code}
The evaluator of the language can be defined as interpretation into the standard model,
for simplicity we only assume it here. Here we use a special case which takes a code
for a \verb$Nat$-endofunction and a natural number.
TODO: use normalisation and its completeness together with decode-encode iso to define
the evaluator and prove its property. Is canonicity enough?
\begin{code}
    eval : ℕ → ℕ → ℕ
    evalProp : (u : Tm ◇ (Nat ⇒ Nat))(n : ℕ) → u $ ⌜ n ⌝ ≡ ⌜ eval (code u) n ⌝
\end{code}
The evaluator is not definable. The proof uses Cantor's diagonal argument.
\begin{code}
  evalNotDefinable : Definable' eval → Lift ⊥
  evalNotDefinable (t , f) = mk (t≠suct (
     ⌜ eval (code u) (code u) ⌝
       ≡⟨ evalProp u (code u) ⁻¹ ⟩
     u $ ⌜ code u ⌝
       ≡⟨ ⇒β ⟩
     suco (t [ p ] $ v0 $ v0) [ ⟨ ⌜ code u ⌝ ⟩ ]
       ≡⟨ suc[] ⟩
     suco ((t [ p ] $ v0 $ v0) [ ⟨ ⌜ code u ⌝ ⟩ ])
       ≡⟨ cong suco $[] ⟩
     suco (((t [ p ] $ v0) [ ⟨ ⌜ code u ⌝ ⟩ ] $ v0 [ ⟨ ⌜ code u ⌝ ⟩ ]))
       ≡⟨ cong (λ x → suco (x $ v0 [ ⟨ ⌜ code u ⌝ ⟩ ])) $[] ⟩
     suco ((t [ p ] [ ⟨ ⌜ code u ⌝ ⟩ ] $ v0 [ ⟨ ⌜ code u ⌝ ⟩ ] $ v0 [ ⟨ ⌜ code u ⌝ ⟩ ]))
       ≡⟨ cong (λ x → suco ((t [ p ] [ ⟨ ⌜ code u ⌝ ⟩ ] $ x $ x))) vz[⟨⟩] ⟩
     suco ((t [ p ] [ ⟨ ⌜ code u ⌝ ⟩ ] $ ⌜ code u ⌝ $ ⌜ code u ⌝))
       ≡⟨ cong (λ x → suco ((x $ ⌜ code u ⌝ $ ⌜ code u ⌝))) [p][⟨⟩] ⟩
     suco ((t $ ⌜ code u ⌝ $ ⌜ code u ⌝))
       ≡⟨ cong suco (un (f (code u) (code u))) ⟩
     suco ⌜ eval (code u) (code u) ⌝
       ∎))
    where
      u : Tm ◇ (Nat ⇒ Nat)
      u = lam (suco (t [ p ] $ v0 $ v0))
      open Standard
\end{code}

Summary of non-definability: if there is a surjection from \verb$ℕ$ to \verb$Tm ◇ (Nat ⇒ Nat)$ and the latter is isomorphic to \verb$ℕ → ℕ$, then there is a surjection from $ℕ$ to $ℕ → ℕ$.

TODO: using an isomorphism \verb$ℕ ≅ ℕ × ℕ$ and its internal version \verb$Nat ≅ Nat × Nat$,
we can show a \verb$ℕ ⇒ ℕ ⇒ ℕ$ function is definable iff.\ its \verb$ℕ ⇒ ℕ$ encoded
variant is definable.

\begin{exe}
Show that the constant \verb$3$ function is definable!
\end{exe}

\section{Normalisation}

\begin{code}[hide]
module Norm where
  open import Ind.Syntax
\end{code}

For each inductive type, the constructor becomes a normal form, the destructor becomes
a neutral term. Inductive types act as base types, so all neutral terms of a base type are normal forms.
\begin{code}
  infixl 5 _$Ne_

  data Ne : Con → Ty → Set
  data Nf : Con → Ty → Set
  data Ne where
    varNe      : ∀{Γ A} → Var Γ A → Ne Γ A
    _$Ne_      : ∀{Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    iteBoolNe  : ∀{Γ A} → Nf Γ A → Nf Γ A → Ne Γ Bool → Ne Γ A
    iteNatNe   : ∀{Γ C} → Nf Γ C → Nf (Γ ▹ C) C → Ne Γ Nat → Ne Γ C
    iteUnitNe  : ∀{Γ A} → Nf Γ A → Ne Γ Unit → Ne Γ A
    iteListNe  : ∀{Γ A C} → Nf Γ C → Nf (Γ ▹ A ▹ C) C → Ne Γ (List A) → Ne Γ C
    iteTreeNe  : ∀{Γ A C} → Nf (Γ ▹ A) C → Nf (Γ ▹ C ▹ C) C → Ne Γ (Tree A) → Ne Γ C

  data Nf where
    neuBool   : ∀{Γ} → Ne Γ Bool → Nf Γ Bool
    neuNat    : ∀{Γ} → Ne Γ Nat → Nf Γ Nat
    neuUnit   : ∀{Γ} → Ne Γ Unit → Nf Γ Unit
    neuList   : ∀{Γ A} → Ne Γ (List A) → Nf Γ (List A)
    neuTree   : ∀{Γ A} → Ne Γ (Tree A) → Nf Γ (Tree A)
    lamNf     : ∀{Γ A B} → Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
    trueNf    : ∀{Γ} → Nf Γ Bool
    falseNf   : ∀{Γ} → Nf Γ Bool
    zeroNf    : ∀{Γ} → Nf Γ Nat
    sucNf     : ∀{Γ} → Nf Γ Nat → Nf Γ Nat
    nilNf     : ∀{Γ A} → Nf Γ (List A)
    consNf    : ∀{Γ A} → Nf Γ A → Nf Γ (List A) → Nf Γ (List A)
    leafNf    : ∀{Γ A} → Nf Γ A → Nf Γ (Tree A)
    nodeNf    : ∀{Γ A} → Nf Γ (Tree A) → Nf Γ (Tree A) → Nf Γ (Tree A)

  ⌜_⌝Ne : ∀{Γ A} → Ne Γ A → Tm Γ A
  ⌜_⌝Nf : ∀{Γ A} → Nf Γ A → Tm Γ A
\end{code}
\begin{code}[hide]
  ⌜ varNe x ⌝Ne = var x
  ⌜ t $Ne u ⌝Ne = ⌜ t ⌝Ne $ ⌜ u ⌝Nf
  ⌜ iteBoolNe t f b ⌝Ne = iteBool ⌜ t ⌝Nf ⌜ f ⌝Nf ⌜ b ⌝Ne
  ⌜ iteNatNe z s n ⌝Ne = iteNat ⌜ z ⌝Nf ⌜ s ⌝Nf ⌜ n ⌝Ne
  ⌜ iteUnitNe t u ⌝Ne = iteUnit ⌜ t ⌝Nf ⌜ u ⌝Ne 
  ⌜ iteListNe n c l ⌝Ne = iteList ⌜ n ⌝Nf ⌜ c ⌝Nf ⌜ l ⌝Ne
  ⌜ iteTreeNe l r t ⌝Ne = iteTree ⌜ l ⌝Nf ⌜ r ⌝Nf ⌜ t ⌝Ne
  ⌜ neuBool t ⌝Nf = ⌜ t ⌝Ne
  ⌜ neuNat t ⌝Nf = ⌜ t ⌝Ne
  ⌜ neuUnit t ⌝Nf = ⌜ t ⌝Ne
  ⌜ neuList t ⌝Nf = ⌜ t ⌝Ne
  ⌜ neuTree t ⌝Nf = ⌜ t ⌝Ne
  ⌜ lamNf t ⌝Nf = lam ⌜ t ⌝Nf
  ⌜ trueNf ⌝Nf = true
  ⌜ falseNf ⌝Nf = false
  ⌜ zeroNf ⌝Nf = zeroo
  ⌜ sucNf t ⌝Nf = suco ⌜ t ⌝Nf
  ⌜ nilNf ⌝Nf = nil
  ⌜ consNf t ts ⌝Nf = cons ⌜ t ⌝Nf ⌜ ts ⌝Nf
  ⌜ leafNf t ⌝Nf = leaf ⌜ t ⌝Nf
  ⌜ nodeNf l r ⌝Nf = node ⌜ l ⌝Nf ⌜ r ⌝Nf
\end{code}

\begin{exe}
What are the normal form of the following terms?
\textnormal{
\begin{code}
  t1 : Σsp (Nf (◇ ▹ Nat ⇒ Bool) (Nat ⇒ Bool)) λ v → ⌜ v ⌝Nf ≡ v0
  t2 : Σsp (Nf (◇ ▹ Bool) Bool) λ v → ⌜ v ⌝Nf ≡ v0
  t3 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ v0
  t4 : Σsp (Nf (◇ ▹ Nat) Nat) λ v → ⌜ v ⌝Nf ≡ iteNat v0 v0 v0
  t5 : Σsp (Nf ◇ Nat) λ v → ⌜ v ⌝Nf ≡ iteNat zeroo v0 (suco (suco zeroo))
  t6 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ iteNat false false v0
  t7 : Σsp (Nf ◇ Bool) λ v → ⌜ v ⌝Nf ≡ iteBool false true false
  t8 : Σsp (Nf ◇ Bool) λ v → ⌜ v ⌝Nf ≡ lam (iteNat true false v0) $ zeroo
  t9 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ lam (iteNat true false v0) $ v0
  t10 : Σsp (Nf (◇ ▹ Nat) Bool) λ v → ⌜ v ⌝Nf ≡ lam (iteNat true false v0) $ suco v0
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
