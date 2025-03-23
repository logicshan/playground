\chapter{Bindings}
\label{ch:Def}

\begin{tcolorbox}[title=Learning goals of this chapter]
 Local definitions. Binding, scope, free and bound variables, De Bruijn indices. Abstract binding trees. Contexts, substitutions. Constructors, destructors, computation and uniqueness rules. Main arguments of a destructor. Neutral terms and normal forms, normalisation by induction on terms. Decidability of equality of terms from normalisation. Injectivity and disjointness of constructors but not destructors.
\end{tcolorbox}

In this chapter we extend Razor with local definitions. For
example, we will be able to write \verb$def x := 1 + 2 in x + x$ which we read as
``define \verb$x$ to be \verb$1 + 2$ inside \verb$x + x$'', and it 
will be equal to \verb$(1 + 2) + (1 + 2) = 3 + 3 = 6$.

In general, names are \emph{bound} by symbols which we call
\emph{binders} and each binder has a \emph{scope}. Examples from mathematics: in the
expression $\sum_{x=1}^{10} x^2$, the name $x$ is bound by the binder $\sum$ in the scope of the binder
which is the expression $x^2$. In
$\text{lim}_{x\mapsto \infty} 2^{-x}$, $\text{lim}$ binds $x$ in
$2^{-x}$. In $\int_{0}^{10} 2x^2+x-1 dx$, $\int\dots d$ binds $x$ in
$2x^2+x-1$.  In $\forall x, x + 3 = 3 + x$, $\forall$ binds $x$ in $x
+ 3 = 3 + x$. In \verb$int f(int i) { return(i+1); }$, the function
definition binds \verb$i$ in the function body (the parts between
\verb${$ and \verb$}$). In \verb$def x := 1 + 2 in x + x$, \verb$x$ is
bound by \verb$def$ in $x + x$.

Variables are sometimes called identifiers or simply names. Note that this
notion of variable is not the same as a mutable reference which is
another concept sometimes called variable in programming languages.

The most direct way to formalise binding is to reuse the function space of our
metatheory and add the following new operation to Razor.
\begin{verbatim}
def : {A B : Ty} → Tm A → (Tm A → Tm B) → Tm B
\end{verbatim}
which is more verbosely
\begin{verbatim}
def : {A B : Ty}(u : Tm A)(t : (x : Tm A) → Tm B) → Tm B
\end{verbatim}
and using derivation rule style notation
\[
\infer{\texttt{def t u : Tm B}}{\texttt{u : Tm A} && \texttt{x : Tm A ⊢ t x : Tm B}}
\]
where the horizontal line and \verb$⊢$ are both notations for metatheoretic function space.
We also add the equation
\[
\texttt{def u t  = t u} \hspace{4em}\text{ which is more verbosely }\hspace{4em} \texttt{def u (λ x → t x) = t u}
\]
and says that letting the dependency in \verb$t$ be \verb$u$ is the same as applying the function \verb$t$ to
the value \verb$u$.

Local definitions are good for making programs shorter and easier to
read, e.g.\ instead of \verb$(num 1 + num 2) + (num 1 + num 2)$ we can write the shorter \verb$def (num 1 + num 2) (λ x → x + x)$. In general, instead of \verb$t u$ we can write \verb$def u t$.

This way of formalising bindigs is sometimes called higher-order
abstract syntax or logical framework (LF) style.  The issue with it is
that it does not provide notions of homomorphism and thus
syntax.
The \verb$def$ operation is a \emph{second-order operation}, and algebraic
theories don't allow second-order operations, so the language extended
with \verb$def$ is not an algebraic theory, it is only a second-order
algebraic theory.

However there are ways to translate second-order algebraic theories to
first order ones. The most popular way is adding a new sort of
\emph{contexts} to the language which collects the names that the
binders introduced so far. Another way is using Schönfinkel's
combinators.

\section{Making bindings first order via contexts}

We will show how to introduce contexts for the AST, well-typed and
well-typed quotiented description of the language.

\subsection{Abstract binding trees}

At the level of abstract syntax trees, we add names and \verb$def$ expressions:
\begin{verbatim}
N ::= x | y | z | ...
T ::= N | def N := T in T | true | false | ite T T T | ...
\end{verbatim}

Multiple binders can be used in one expression:
\begin{verbatim}
(def x := t in x + x) + (def y := t' in y + y)
\end{verbatim}
The names of the bound variables have no significance. The above term should be equal to
\begin{verbatim}
(def y := t in y + y) + (def x := t' in x + x)
\end{verbatim}
or 
\begin{verbatim}
(def z := t in z + z) + (def z := t' in z + z)
\end{verbatim}
for any \verb$t$, \verb$t'$. These are different terms at the level of abstract
syntax trees, however, they are equal at the level of \emph{abstract binding trees} (ABTs). 
ABT is between levels (3) and (4) of Chapter \ref{ch:precision},
see Figure \ref{fig:levels}. Names are replaced by pointers to the binding.
The above terms become the following. \\
\begin{tikzpicture}[node distance=0cm]
\node (t1) at (0,0) {(def };
\node[right=of t1] (t2) {□};
\node[right=of t2] (t3) { := t in };
\node[right=of t3] (t4) {○};
\node[right=of t4] (t5) { + };
\node[right=of t5] (t6) {○};
\node[right=of t6] (t7) {) + (def };
\node[right=of t7] (t8) {□};
\node[right=of t8] (t9) {:= t' in };
\node[right=of t9] (t10) {○};
\node[right=of t10] (t11) { + };
\node[right=of t11] (t12) {○};
\node[right=of t12] (t13) {)};
\draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (t4) edge[bend right=60] node {} (t2);
\draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (t6) edge[bend right=90] node {} (t2);
\draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (t10) edge[bend right=60] node {} (t8);
\draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (t12) edge[bend right=90] node {} (t8);
\end{tikzpicture} \\
In tree notation: \\
\begin{tikzpicture}
  \node (x10) at (0,0) {\verb$+$};
  \node (x20) at (-2,-1) {\verb$def$};
  \node (x21) at (2,-1) {\verb$def$};
  \node (x30) at (-3,-2) {\verb$t$};
  \node (x31) at (-1,-2) {\verb$+$};
  \node (x32) at (1,-2) {\verb$t'$};
  \node (x33) at (3,-2) {\verb$+$};
  \node (x40) at (-1.5,-3) {\verb$○$};
  \node (x41) at (-0.5,-3) {\verb$○$};
  \node (x42) at (2.5,-3) {\verb$○$};
  \node (x43) at (3.5,-3) {\verb$○$};
  \draw[-] (x10) edge node {} (x20);
  \draw[-] (x10) edge node {} (x21);
  \draw[-] (x20) edge node {} (x30);
  \draw[-] (x20) edge node {} (x31);
  \draw[-] (x21) edge node {} (x32);
  \draw[-] (x21) edge node {} (x33);
  \draw[-] (x31) edge node {} (x40);
  \draw[-] (x31) edge node {} (x41);
  \draw[-] (x33) edge node {} (x42);
  \draw[-] (x33) edge node {} (x43);
  \draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (x40) edge[bend left=30] node {} (x20);
  \draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (x41) edge[bend right=50] node {} (x20);
  \draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (x42) edge[bend left=30] node {} (x21);
  \draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (x43) edge[bend right=50] node {} (x21);
\end{tikzpicture}

The scope of \verb$def$ is the longest possible, so the
 scope of both \verb$def$s end at the end of the term.

Another example:
\begin{verbatim}
def x := t in (x + x) + def y := t' in x + y
\end{verbatim}
Binding structure: \\
\begin{tikzpicture}[node distance=0cm]
\node (t1) at (0,0) {def };
\node[right=of t1] (t2) {□};
\node[right=of t2] (t3) { := t in };
\node[right=of t3] (t4) {(○};
\node[right=of t4] (t5) { + };
\node[right=of t5] (t6) {○)};
\node[right=of t6] (t7) { + def };
\node[right=of t7] (t8) {□};
\node[right=of t8] (t9) {:= t' in };
\node[right=of t9] (t10) {○};
\node[right=of t10] (t11) { + };
\node[right=of t11] (t12) {○};
\node[right=of t12] (t13) {};
\draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (t4) edge[bend right=60] node {} (t2);
\draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (t6) edge[bend right=90] node {} (t2);
\draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (t10) edge[bend right=40] node {} (t2);
\draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (t12) edge[bend right=90] node {} (t8);
\end{tikzpicture} \\
In tree notation: \\
\begin{tikzpicture}
  \node (x10) at (0,0) {\verb$def$};
  \node (x20) at (-2,-1) {\verb$t$};
  \node (x21) at (2,-1) {\verb$+$};
  \node (x30) at (1,-2) {\verb$+$};
  \node (x31) at (3,-2) {\verb$def$};
  \node (x40) at (0.5,-3) {\verb$○$};
  \node (x41) at (1.5,-3) {\verb$○$};
  \node (x42) at (2.5,-3) {\verb$t'$};
  \node (x43) at (3.5,-3) {\verb$+$};
  \node (x50) at (3,-4) {\verb$○$};
  \node (x51) at (4,-4) {\verb$○$};
  \draw[-] (x10) edge node {} (x20);
  \draw[-] (x10) edge node {} (x21);
  \draw[-] (x21) edge node {} (x30);
  \draw[-] (x21) edge node {} (x31);
  \draw[-] (x30) edge node {} (x40);
  \draw[-] (x30) edge node {} (x41);
  \draw[-] (x31) edge node {} (x42);
  \draw[-] (x31) edge node {} (x43);
  \draw[-] (x43) edge node {} (x50);
  \draw[-] (x43) edge node {} (x51);
  \draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (x40) edge[bend left=30] node {} (x10);
  \draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (x41) edge[bend right=50] node {} (x10);
  \draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (x50) edge[bend left=30] node {} (x10);
  \draw[arrows={-Triangle[angle=70:7pt]},densely dotted] (x51) edge[bend right=50] node {} (x31);
\end{tikzpicture}

The term \verb$(def x := t in x + x) + (def y := t' in x + y)$ is different from both of the
above terms, it contains a \emph{free} name \verb$x$ in \verb$x + y$. Free variables
are not in the scope of a binder which binds the same name. A term is called \emph{closed} if
there are no free variables in it, \emph{open} if it contains at least one free variable.
Every open term can be closed by adding enough binders at the front.

One way to make abstract binding trees precise is to add the following equation:
\begin{verbatim}
(def x:=t in u) = (def y:=t in u[x↦y])
\end{verbatim}
where \verb$u[x↦y]$ means that we replace all occurrences of \verb$x$ by \verb$y$ in \verb$u$.
However one has to be careful:
\begin{verbatim}
(def x:=t in x + y) ≠ (def y:=t in y + y) = (def y:=t in (x + y)[x↦y])
\end{verbatim}
The left-hand side term is open, the right-hand side is closed, so they
cannot have the same binding tree. In the equation above it has to
be stated that \verb$y$ is fresh for \verb$u$ (\verb$u$ does not contain \verb$y$).
See e.g.\ \cite[Section 1.2]{harper} for details on that approach.

Another approach to define abstract binding trees takes it seriously
that the names of bound variables don't matter and does not write names at
all. Instead, we write natural numbers (De Bruijn indices \cite{debruijn}). Examples:
\begin{verbatim}
(def x:=t in x + x) + (def y:=t' in y + y)         (def t in v0 + v0) + (def t' in v0 + v0)
def x:=t in (x + x) + def y:=t' in x + y            def t in (v0 + v0) + def t' in  v1 + v0
\end{verbatim}
\verb$v0$ is a reference to the nearest binder, \verb$v1$ is a reference to 
the next one, and so on.

Now terms are indexed by natural numbers expressing the maximal number
of free variables in them. 
\begin{itemize}
  \item \verb$Tm 0$ is the set of closed terms (programs).
  \item \verb$Tm 1$ is the set of terms which can refer to one free variable.
  \item \verb$Tm 2$ is the set of terms which can refer to two different free variables.
  \item \verb$Tm 3$ is the set of terms which can refer to three different free variables.
  \item \dots
\end{itemize}
Binders are those operators which decrease this
number: e.g.\ \verb$def$ takes a \verb$Tm (1 + n)$ in which it binds the
variable and returns a \verb$Tm n$. Examples:
\[
\verb$if false then num 0 else num 3 : Tm 0$
\]
\SaveVerb{verb1}|(v0 + v0)|
\[
 \verb$def t $ \underbrace{\UseVerb{verb1}}_{\verb$: Tm 1$}\verb$ + def t' $\underbrace{\UseVerb{verb1}}_{\verb$: Tm 1$}\verb$ : Tm 0$
\]
\SaveVerb{verb2}|((v0 + v0) + def t' |
\SaveVerb{verb3}|(v1 + v0)|
\SaveVerb{verb4}|)|
\SaveVerb{verb5}|: Tm 2|
\[
\verb$def t $\underbrace{\UseVerb{verb2}\underbrace{\UseVerb{verb3}}_{\UseVerb{verb5}}\UseVerb{verb4}}_{\verb$: Tm 1$}\verb$ : Tm 0$
\]

We have a separate set \verb$Var n$ of variables which are included in
terms. A DefABT model:
\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module DefABT where

open import Lib hiding (_∘_ ; _,_)

module I where
  infixl 7 _+o_
  data Var  : ℕ → Set where
    vz      : ∀{n} → Var (suc n)
    vs      : ∀{n} → Var n → Var (suc n)

  data Tm   : ℕ → Set where
    var     : ∀{n} → Var n → Tm n
    def     : ∀{n} → Tm  n → Tm (suc n) → Tm n
    
    true    : ∀{n} → Tm n
    false   : ∀{n} → Tm n
    ite     : ∀{n} → Tm n → Tm n → Tm n → Tm n
    num     : ∀{n} → ℕ → Tm n
    isZero  : ∀{n} → Tm n → Tm n
    _+o_    : ∀{n} → Tm n → Tm n → Tm n
    
  v0 : {n : ℕ} → Tm (1 + n)
  v0 = var vz
  v1 : {n : ℕ} → Tm (2 + n)
  v1 = var (vs vz)
  v2 : {n : ℕ} → Tm (3 + n)
  v2 = var (vs (vs vz))
  v3 : {n : ℕ} → Tm (4 + n)
  v3 = var (vs (vs (vs vz)))
\end{code}
\begin{code}
record Model {ℓ ℓ'} : Set (lsuc (ℓ ⊔ ℓ')) where
  infixl 7 _+o_
  field
    Var : ℕ → Set ℓ
    vz : ∀{n} → Var (suc n)
    vs : ∀{n} → Var n → Var (suc n)

    Tm      : ℕ → Set ℓ'
    var     : ∀{n} → Var n → Tm n
    def     : ∀{n} → Tm  n → Tm (suc n) → Tm n
    true    : ∀{n} → Tm n
    false   : ∀{n} → Tm n
    ite     : ∀{n} → Tm n → Tm n → Tm n → Tm n
    num     : ∀{n} → ℕ → Tm n
    isZero  : ∀{n} → Tm n → Tm n
    _+o_    : ∀{n} → Tm n → Tm n → Tm n
\end{code}
We have two iterators, one for each sort:
\begin{code}
  ⟦_⟧v : ∀{n} → I.Var n → Var n
  ⟦ I.vz ⟧v = vz
  ⟦ I.vs v ⟧v = vs ⟦ v ⟧v

  ⟦_⟧t : ∀{n} → I.Tm n → Tm n
  ⟦ I.var x ⟧t = var ⟦ x ⟧v
  ⟦ I.def x t ⟧t = def ⟦ x ⟧t ⟦ t ⟧t
  ⟦ I.true ⟧t = true
  ⟦ I.false ⟧t = false
  ⟦ I.ite t tr fa ⟧t = ite ⟦ t ⟧t ⟦ tr ⟧t ⟦ fa ⟧t
  ⟦ I.num x ⟧t = num x
  ⟦ I.isZero t ⟧t = isZero ⟦ t ⟧t
  ⟦ l I.+o r ⟧t = ⟦ l ⟧t +o ⟦ r ⟧t
\end{code}
Some abbreviations:
\begin{code}
  v0 : {n : ℕ} → Tm (1 + n)
  v0 = var vz
  v1 : {n : ℕ} → Tm (2 + n)
  v1 = var (vs vz)
  v2 : {n : ℕ} → Tm (3 + n)
  v2 = var (vs (vs vz))
  v3 : {n : ℕ} → Tm (4 + n)
  v3 = var (vs (vs (vs vz)))
\end{code}
\begin{code}[hide]
open I
t : Tm 0
t' : Tm 0
\end{code}
Formal version of the term \verb$(def x:=1+2 in x+x) + (def y:=3+4 in y+y)$.
\begin{code}
t = def (num 1 +o num 2) (v0 +o v0) +o def (num 3 +o num 4) (v0 +o v0)
\end{code}
Formal version of the term \verb$def x:=1+2 in ((x+x) + def y:=3+4 in x+y)$.
\begin{code}
t' = def (num 1 +o num 2) ((v0 +o v0) +o def (num 3 +o num 4) (v1 +o v0))
\end{code}

Note that in our formal syntax we don't have variable names, so there
is no function which extracts the names of the free variables from a
term.

\begin{code}[hide]
record DepModel {ℓ ℓ'} : Set (lsuc (ℓ ⊔ ℓ')) where
  infixl 7 _+o∙_
  field
    Var∙ : ∀{n} → I.Var n → Set ℓ
    vz∙  : ∀{n} → Var∙ (I.vz {n})
    vs∙  : ∀{n v} → Var∙ {n} v → Var∙ (I.vs v)
    Tm∙  : ∀{n} → I.Tm n → Set ℓ'
    var∙     : ∀{n v} → Var∙ {n} v → Tm∙ (I.var v)
    def∙     : ∀{n t t'} → Tm∙ {n} t → Tm∙ {suc n} t' → Tm∙ (I.def t t')
    true∙    : ∀{n} → Tm∙ {n} I.true 
    false∙   : ∀{n} → Tm∙ {n} I.false
    ite∙     : ∀{n t tr fa} → Tm∙ {n} t → Tm∙ tr → Tm∙ fa → Tm∙ (I.ite t tr fa)
    num∙     : ∀{n} → (m : ℕ) → Tm∙ {n} (I.num m)
    isZero∙  : ∀{n t} → Tm∙ {n} t → Tm∙ (I.isZero t)
    _+o∙_    : ∀{n l r} → Tm∙ {n} l → Tm∙ r → Tm∙ (l I.+o r)
  
  ⟦_⟧v : ∀{n} → (v : I.Var n) → Var∙ v
  ⟦ vz ⟧v = vz∙
  ⟦ vs v ⟧v = vs∙ ⟦ v ⟧v

  ⟦_⟧t : ∀{n} → (t : I.Tm n) → Tm∙ t
  ⟦ var x ⟧t = var∙ ⟦ x ⟧v
  ⟦ def t t' ⟧t = def∙ ⟦ t ⟧t ⟦ t' ⟧t
  ⟦ true ⟧t = true∙
  ⟦ false ⟧t = false∙
  ⟦ ite t tr fa ⟧t = ite∙ ⟦ t ⟧t ⟦ tr ⟧t ⟦ fa ⟧t
  ⟦ num x ⟧t = num∙ x
  ⟦ isZero t ⟧t = isZero∙ ⟦ t ⟧t
  ⟦ l +o r ⟧t = ⟦ l ⟧t +o∙ ⟦ r ⟧t
\end{code}

\begin{exe}[compulsory]
  In the following ABT-level syntactic terms, circle the free variables. From bound variables, draw a pointer
  to the binder.
  \begin{verbatim}
  x + y

  x + def x := 3 in y + x

  x + def x := y in y + x

  x + def x := x' + (x + def x' := z in x' + x)

  3 + def x := x + (x' + def x' := 2 in x' + x)
  \end{verbatim}
\end{exe}

\begin{exe}[compulsory]
  Decide whether the following ABT-level syntactic terms are equal.
  \begin{verbatim}
  x + y ‌≟ x + z
  (x + def x := 3 in x + y) ≟ (x + def y := 3 in y + y)
  (x + def x := 3 in x + y) ≟ (x + def y := 3 in y + x)
  (x + def x := 3 in x + y) ≟ (x + def x' := 3 in x' + y)
  (x + def x := 3 in def y := 4 in x + y) ≟ (x + def y := 3 in def x := 4 in x + y)
  (x + def x := 3 in def y := 4 in x + y) ≟ (x + def y := 3 in def x := 4 in y + x)
  \end{verbatim}
\end{exe}

\begin{exe}[compulsory]
  Decide whether the following ABT-level syntactic terms are open or closed.
  \begin{verbatim}
  def x := 3 in x + x
  def x := y in x + x
  def x := y in x + y
  def y := x in x + y
  def y := x in x + x
  \end{verbatim}
\end{exe}

\begin{exe}[compulsory]
  Rewrite the following (closed) terms with De Bruijn notation.
\begin{verbatim} 
  def x:=1 in x + def y:=x+1 in y + def z:=x+y in (x+z)+(y+x)
  (def x:=1 in x) + def y:=1 in y + def z:=1+y in z+(y+1)
  (def x:=1 in x + def y:=x+1 in y) + def z:=1 in z+z
  (def x:=1 in x) + (def y:=1 in y) + def z:=1 in z+z
\end{verbatim} 
\end{exe}

\begin{exe}[compulsory]
  Rewrite the following (closed) terms with variable name notation.
{\normalfont
\begin{code}[hide]
t1 t2 t3 t4 : Tm 0
\end{code}
\begin{code}
t1 = def true (v0 +o def v0 (v0 +o v1))
t2 = def true (def false (ite v0 v0 v1))
t3 = true +o def true (false +o def v0 (v1 +o v0))
t4 = def true (def false (def true (def false ((v0 +o v1) +o (v2 +o v3)))))
\end{code}
}
\end{exe}

\begin{code}[hide]
data Vec {i}(A : Set i) : ℕ → Set i where
  [] : Vec A zero
  _::_ : A → {n : ℕ} → Vec A n → Vec A (suc n)
infixr 5  _::_

infixr 5 _++_
_++_ : ∀{i n m}{A : Set i} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

[_] : ∀{i}{A : Set i} → A → Vec A 1
[ x ] = x :: []
\end{code}

\begin{exe}[recommended]
  Write a function which returns the number of occurrences of each variable in a term:
{\normalfont
\begin{code}
countVars : {n : ℕ} → Tm n → Vec ℕ n
\end{code}
}
  For example it should work as follows:
{\normalfont
\begin{code}
countVarsTest1 : countVars {1} ((v0 +o v0) +o v0) ≡ 3 :: []
countVarsTest2 : countVars {2} ((v1 +o v1) +o v0) ≡ 1 :: 2 :: []
countVarsTest3 : countVars {2} ((v0 +o v0) +o v1) ≡ 2 :: 1 :: []
countVarsTest4 : countVars {3} ((v2 +o v0) +o v1) ≡ 1 :: 1 :: 1 :: []
\end{code}
\begin{code}[hide]
countVars = exercise
countVarsTest1 = exercisep
countVarsTest2 = exercisep
countVarsTest3 = exercisep
countVarsTest4 = exercisep
\end{code}
}
\end{exe}
