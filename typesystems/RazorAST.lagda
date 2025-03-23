\part{What is a programming language?}

\chapter{Levels of abstraction}
\label{ch:precision}

\begin{tcolorbox}[title=Learning goals of this chapter]
  \begin{itemize}
  \item Levels of abstraction when defining a programming language: strings, sequences of lexical elements, abstract syntax trees, well-typed syntax, well-typed syntax with equations
  \item Meta language, object language
  \item Model, syntax, defining functions by iteration
  \item Dependent model, proving properties by induction
  \item Disjointness and injectivity of syntactic operators, finiteness of elements of the syntax
  \item Trivial model, C-style standard model
  \item Type inference
  \item Standard model and the standard interpreter
  \item Derivable and admissible operators and equations
  \item Equational consistency
  \item Normalisation, its completeness and stability
  \end{itemize}
\end{tcolorbox}

In this chapter, we study a very simple programming language called Razor (as an hom{\`a}ge to Hutton's razor \cite{razor}) which contains e.g.\ the following program.
\begin{verbatim}
if isZero (num 0 + num 1) then false else isZero (num 0)
\end{verbatim}
A Razor program is either a numeric or a boolean expression. Numbers can
be formed using \verb$num i$ where \verb$i$ is a natural number. Booleans are
\verb$true$ or \verb$false$. We have the usual if-then-else operator, addition
and an isZero operator which says whether a number is 0. The above
program evaluates in the following steps (each new line is a step).
\begin{verbatim}
if isZero (num 0 + num 1) then false else isZero (num 0)
if isZero (num 1) then false else isZero (num 0)
if false then false else isZero (num 0)
isZero (num 0)
true
\end{verbatim}

We will describe this language in several iterations. Each iteration
will be a more precise but also more abstract description of the language: strings,
sequences of lexical elements, abstract syntax trees, well-typed
syntax and well-typed syntax with equations.

See Figures \ref{fig:levels}, \ref{fig:levels1}.

\begin{figure}
\begin{center}
\def\excludePos{-2.6} % -4.9
\def\quotientByPos{-2.6}
\begin{tikzpicture}
%\node[inner sep=0pt] (img) at (-9.5,6){\includegraphics[width=5.5cm]{levels.png}};
\node            (lab1) at (0,12) {\textbf{level}};
\node[left,red]  (lab2) at (\excludePos,11.5) {exclude\vphantom{g}};
\node[gray]      (lab3) at (-1.2,11) {going abstract};
\node[gray]      (lab4) at (1.4,11) {going concrete};
\node[left]      (lab5) at (\quotientByPos,11) {quotient by};
\node (str) at (0,0) {\textbf{(1) string}};
\node (lex) at (0,2) {\textbf{(2) sequence of lexical elements}};
\node (ast) at (0,4) {\textbf{(3) abstract syntax tree}};
\node (abt) at (0,6)  {\textbf{abstract binding tree}};
\node (wt)  at (0,8) {\textbf{(4) well typed syntax}};
\node (alg) at (0,10) {\textbf{(5) well typed syntax with equations}};
\path[->] (str.north) edge [bend left] node[gray, left] {lexical analysis} (lex.south);
\path[->] (lex.north) edge [bend left] node[gray, left] {parsing} (ast.south);
\path[->] (ast.north) edge [bend left] node[gray, left] {scope checking} (abt.south);
\path[->] (abt.north) edge [bend left] node[gray, left] {type checking} (wt.south);
\path[->] (wt.north)  edge [bend left] node[gray, left] {} (alg.south);
\node (lex1) at (\excludePos,0.5) {};
\node (ast1) at (\excludePos,2.5) {};
\node (abt1) at (\excludePos,4.5) {};
\node (wt1)  at (\excludePos,6.5) {};
\node (alg1) at (\excludePos,8.5) {};
\path[->] (str.north) edge [bend right=15] node[red, left, pos=1] {invalid lexical elements} (lex1.west);
\path[->] (lex.north) edge [bend right=15] node[red, left, pos=1] {bad number of parameters} (ast1.west);
\path[->] (ast.north) edge [bend right=15] node[red, left, pos=1] {variable not in scope} (abt1.west);
\path[->] (abt.north) edge [bend right=15] node[red, left, pos=1] {non-matching types} (wt1.west);
\draw[->] (lex) edge [bend left] node[gray, right] {add spaces} (str);
\draw[->] (ast) edge [bend left] node[gray, right] {add brackets} (lex);
\draw[->] (abt) edge [bend left] node[gray, right] {pick variable names} (ast);
\draw[->] (wt)  edge [bend left] node[gray, right] {} (abt);
\draw[->] (alg) edge [bend left] node[gray, right] {normalise} (wt);
\node[left] (qstr) at (\quotientByPos,1) {removal of spaces};
\node[left] (qlex) at (\quotientByPos,3) {removal of extra brackets};
\node[left] (qast) at (\quotientByPos,5) {renaming of bound variables};
\node[left] (qabt) at (\quotientByPos,7) {};
\node[left] (qwt)  at (\quotientByPos,9) {operational equivalence};
\end{tikzpicture}
\end{center}
\caption{Different levels of abstraction when defining a programming language and transformations between levels.
At more abstract levels, certain programs are excluded and others identified. Abstract binding trees are sometimes called well-scoped syntax trees, see chapter \ref{ch:def} (they are not relevant for the Razor language).}
\label{fig:levels} \end{figure}

\begin{figure}
\begin{minipage}[t]{0.4\textwidth}
\includegraphics[width=6cm]{levels.png}
\end{minipage}
\begin{minipage}[b]{0.4\textwidth}
\begin{alignat*}{10}
& \rlap{(5) well-typed syntax with equations} \\
& \hspace{1.6em} && \texttt{Ty}   && \texttt{: Set} \\
& && \texttt{Tm}   && \texttt{: Ty → Set} \\
& && \texttt{Bool}   && \texttt{: Ty} \\
& && \texttt{Nat}   && \texttt{: Ty} \\
& && \texttt{true}   && \texttt{: Tm Bool} \\
& && \texttt{false}   && \texttt{: Tm Bool} \\
& && \texttt{ite}   && \texttt{: Tm Bool → Tm A → Tm A → Tm A} \\
& && \texttt{num}   &&  \texttt{: ℕ → Tm Nat} \\
& && \texttt{isZero }  && \texttt{: Tm Nat → Tm Bool} \\
& && \texttt{\_+\_}    && \texttt{: Tm Nat → Tm Nat → Tm Nat} \\
& && \texttt{iteβ₁}    && \texttt{: ite true u v = u} \\
& && \texttt{iteβ₂}    && \texttt{: ite false u v = v} \\
& && \texttt{isZeroβ₁} && \texttt{: isZero (num 0) = true} \\
& && \texttt{isZeroβ₂ } && \texttt{: isZero (num (1+n)) = false} \\
& && \texttt{+β} && \texttt{: num m + num n = num (m + n)} \\
& \rlap{(4) well-typed syntax} \\
& && \texttt{Ty}   && \texttt{: Set} \\
& && \texttt{Tm}   && \texttt{: Ty → Set} \\
& && \texttt{Bool}   && \texttt{: Ty} \\
& && \texttt{Nat}   && \texttt{: Ty} \\
& && \texttt{true}   && \texttt{: Tm Bool} \\
& && \texttt{false}   && \texttt{: Tm Bool} \\
& && \texttt{ite}   && \texttt{: Tm Bool → Tm A → Tm A → Tm A} \\
& && \texttt{num}   &&  \texttt{: ℕ → Tm Nat} \\
& && \texttt{isZero }  && \texttt{: Tm Nat → Tm Bool} \\
& && \texttt{\_+\_}    && \texttt{: Tm Nat → Tm Nat → Tm Nat} \\
& \rlap{(3) abstract syntax tree} \\
& && \texttt{Tm}   && \texttt{: Set} \\
& && \texttt{true}   && \texttt{: Tm} \\
& && \texttt{false}   && \texttt{: Tm} \\
& && \texttt{ite}   && \texttt{: Tm → Tm → Tm → Tm} \\
& && \texttt{num}   &&  \texttt{: ℕ → Tm} \\
& && \texttt{isZero}  && \texttt{: Tm → Tm} \\
& && \texttt{\_+\_}    && \texttt{: Tm → Tm → Tm} \\
& \rlap{(2) list of the following lexical elements:} \\
& && \rlap{$\texttt{(, ), true, false, if, then, else, num, isZero, +, 0, 1, 2, 3, ...}$} \\
& \rlap{(1) any string}
\end{alignat*}
\end{minipage}
\caption{Left: example Razor programs at different levels of abstraction. Each bubble represents a separate program. Right: description of the Razor expression language at levels (1)--(5).}
\label{fig:levels1} \end{figure}


\section{String}

As a first approximation, we say that a program is a string, that is,
a sequence of (ASCII) characters. This is how we write programs on a
computer. Any string is a program.

Many strings do not correspond to meaningful programs in our language
such as \verb$num 3 - num 2$ as we don't have subtraction. Also, there
are different strings which represent the same program. For example,
\verb$isZero (num 1)$ and \verb$isZero     (num 1)$ are different as
strings but should be the same programs as the extra spaces after
\verb$isZero$ shouldn't matter.

Instead of describing which strings are meaningful programs and
defining an equivalence relation for identifying strings that
represent the same program, we will describe programs using a more
abstract structure.

\section{Sequence of lexical elements}

We describe Razor by the following lexical elements.
\[
\verb$($, \verb$)$, \verb$true$, \verb$false$, \verb$if$, \verb$then$,
\verb$else$, \verb$num$, \verb$isZero$, \verb$+$, \verb$0$, \verb$1$, \verb$2$, \verb$...$
\]
The \verb$...$ part means that any natural number is a lexical element.
A program is an arbitrary sequence made of these.

Our example program
\[
\verb$if isZero (num 0 + num 1) then false else isZero (num 0)$
\]
is the following sequence.
\[
[\verb$if$, \verb$isZero$, \verb$($, \verb$num$, \verb$0$, \verb$+$,
\verb$num$, \verb$0$, \verb$)$, \verb$then$, \verb$false$,
\verb$else$, \verb$isZero$, \verb$($, \verb$num$, \verb$0$, \verb$)$]
\]

Now we have much fewer programs and \verb$num 3 - num 2$ is
not a program anymore because there is no lexical element for \verb$-$. Any two programs given as strings which differ
only in the number of spaces will end up as the same program at this
level: \verb$isZero (num 1)$ and \verb$isZero     (num 1)$ are both
given by the sequence [\verb$isZero$, \verb$($, \verb$num$, \verb$1$, \verb$)$].

However, we still have meaningless programs, e.g. [\verb$($,
\verb$true$] (there is no closing parenthesis) or [\verb$num$,
\verb$1$, \verb$+$] (\verb$+$ needs two arguments), and so
on. Also, there are programs which could be identified, e.g.\
[\verb$($, \verb$true$, \verb$)$] and [\verb$true$] (the parentheses are redundant in the former).

Again, to solve these issues, we move to a higher-level representation
of programs.

Note that we can always obtain a string from a sequence of lexical
elements by simply printing the sequence. In the other direction, we
can implement a lexical analyser (lexer) which turns a string into a
sequence of lexical elements or returns an error.

For convenience, we usually write strings instead of lists of lexical
elements. In this case, we specify that we are interpreting the strings
as lists of lexical elements.

\begin{exe}[compulsory]
Which equations of lists of lexical elements hold?
\begin{verbatim}
num    3 ≟ num(3)
isZero 0 ≟ true
if 3 then (false) ≟ if    3   then (   false)
(if 3 then (false)) ≟ if    3   then (   false)
then then if ‌≟ then   then if
\end{verbatim}
\end{exe}

\begin{exe}[compulsory]
Mark those strings for which the lexical analyser outputs an error. For those
strings that are accepted, write down the list of lexical elements it outputs.
\begin{verbatim}
if true then true else num 0
if true then num 0 else num 0
if num 0 then num 0 else num 0
if if then num 0 else num 0
true + zero
true + num 1
true + isZero
isZero + 0
\end{verbatim}
\end{exe}

\begin{exe}
  Write a lexical analyser for Razor: the input is a string, the output is either a sequence of lexical elements or an error.
\end{exe}

\section{Abstract syntax tree}

We define our language by the following BNF grammar (where \verb$N$ means a natural number):
\begin{verbatim}
  T ::= true | false | if T then T else T | num N | isZero T | T + T
\end{verbatim}
In Haskell, we would write this as follows (using \verb$Int$ for natural numbers).
\begin{verbatim}
  data Tm = True | False | Ite Tm Tm Tm | Num Int | IsZero Tm | Tm :+: Tm
\end{verbatim}
We will use the following Agda notation for the same definition. Here every operator is followed by its \emph{arity}: the number of arguments it takes.
We call elements of \verb$Tm$ terms. We write \verb$ite$ instead of if-then-else and \verb$+o$ instead of $+$ for convenience.
\begin{code}[hide]
{-# OPTIONS --prop --rewriting #-}
module RazorAST where

open import Lib
module I where

  infixl 7 _+o_
\end{code}
\begin{code}
  data Tm   : Set where
    true    : Tm
    false   : Tm
    ite     : Tm → Tm → Tm → Tm
    num     : ℕ → Tm
    isZero  : Tm → Tm
    _+o_    : Tm → Tm → Tm
\end{code}
In this description, we added the information that if-then-else has three,
isZero one and addition two \verb$Tm$
arguments while \verb$num$ has a natural number argument. Programs are now trees which have \verb$true$, \verb$false$
or \verb$num i$ at their leaves and they can have ternary branching with
\verb$ite$ at the branching node, unary branching with \verb$isZero$ at the node or binary branching with \verb$+$ at the
node.

Our example program
\[
\verb$if isZero (num 0 + num 1) then false else isZero (num 0)$
\]
is depicted as follows.

\begin{tikzpicture}
  \node (x10) at (0,0) {\verb$ite$};
  \node (x20) at (-1,-1) {\verb$isZero$};
  \node (x21) at (0,-1) {\verb$false$};
  \node (x22) at (1,-1) {\verb$isZero$};
  \node (x30) at (-1,-2) {\verb$+$};
  \node (x31) at (1,-2) {\verb$num 0$};
  \node (x40) at (-1.7,-3) {\verb$num 1$};
  \node (x41) at (-0.3,-3) {\verb$num 0$};
  \draw[-] (x10) edge node {} (x20);
  \draw[-] (x10) edge node {} (x21);
  \draw[-] (x10) edge node {} (x22);
  \draw[-] (x20) edge node {} (x30);
  \draw[-] (x22) edge node {} (x31);
  \draw[-] (x30) edge node {} (x40);
  \draw[-] (x30) edge node {} (x41);
\end{tikzpicture}

Instead of drawing trees we usually use linear notation to save space:
\begin{code}[hide]
ex =
\end{code}
\begin{code}
  ite (isZero (num 0 +o num 1)) false (isZero (num 0))
\end{code}
\begin{code}[hide]
  where open I
\end{code}
Programs such as \verb$(true$ and \verb$num 1 +$ which were valid as sequences of
lexical elements do not correspond to any tree, and the programs \verb$(true)$ and
\verb$true$ correspond to the same tree.

Note that \verb$(num 0 + num 0) + num 0$ and
\verb$num 0 + (num 0 + num 0)$ are different trees.

\begin{tikzpicture}
  \node (x10) at (0,0) {\verb$+$};
  \node (x20) at (-0.7,-1) {\verb$+$};
  \node (x21) at (0.7,-1) {\verb$num 0$};
  \node (x30) at (-1.4,-2) {\verb$num 0$};
  \node (x31) at (0,-2) {\verb$num 0$};
  \draw[-] (x10) edge node {} (x20);
  \draw[-] (x10) edge node {} (x21);
  \draw[-] (x20) edge node {} (x30);
  \draw[-] (x20) edge node {} (x31);
  \node (y10) at (4,0) {\verb$+$};
  \node (y20) at (3.3,-1) {\verb$num 0$};
  \node (y21) at (4.7,-1) {$+$};
  \node (y30) at (4,-2) {\verb$num 0$};
  \node (y31) at (5.4,-2) {\verb$num 0$};
  \draw[-] (y10) edge node {} (y20);
  \draw[-] (y10) edge node {} (y21);
  \draw[-] (y21) edge node {} (y30);
  \draw[-] (y21) edge node {} (y31);
\end{tikzpicture}

Even if the intuitive meaning of both is the number zero, they are
different as trees. An example of parentheses which even changes the
intuitive meaning of an expression is $1+(2*3) = 7 ≠ 9 = (1+2)*3$ (this example is not in the Razor language as it has multiplication).

The \emph{meta theory} (meta language) is the language that we use to
speak about the \emph{object theory} (object language). Our meta
language is Agda (and sometimes English but we can translate all of
our English arguments to Agda), our object language is Razor.

\begin{exe}[compulsory]
  Draw the trees depicting the following programs:
\begin{verbatim}
(true + true) + true
((true + true) + true) + true
(true + (true + true)) + true
true + ((true + true) + true)
ite (true + true) ((true + true) + true) (true + (true + true))
\end{verbatim}
\end{exe}

\begin{exe}[compulsory]
  Write down the following tree with linear notation: \\
  \begin{tikzpicture}
  \node (x10) at (0,0) {\verb$ite$};
  \node (x20) at (-2,-1) {\verb$+$};
  \node (x21) at (0,-1) {\verb$num 0$};
  \node (x22) at (2,-1) {\verb$ite$};
  \node (x30) at (-2.7,-2) {\verb$num 0$};
  \node (x31) at (-1.3,-2) {\verb$isZero$};
  \node (x32) at (1,-2) {\verb$+$};
  \node (x33) at (2,-2) {\verb$num 3$};
  \node (x34) at (3,-2) {\verb$true$};
  \node (x40) at (-1.3,-3) {\verb$num 2$};
  \node (x41) at (0.5,-3) {\verb$true$};
  \node (x42) at (1.5,-3) {\verb$false$};
  \draw[-] (x10) edge node {} (x20);
  \draw[-] (x10) edge node {} (x21);
  \draw[-] (x10) edge node {} (x22);
  \draw[-] (x20) edge node {} (x30);
  \draw[-] (x20) edge node {} (x31);
  \draw[-] (x22) edge node {} (x32);
  \draw[-] (x22) edge node {} (x33);
  \draw[-] (x22) edge node {} (x34);
  \draw[-] (x31) edge node {} (x40);
  \draw[-] (x32) edge node {} (x41);
  \draw[-] (x32) edge node {} (x42);
\end{tikzpicture}
\end{exe}

\begin{exe}[compulsory]
Here are some lists of lexical elements (written as strings). Which ones are accepted by the parser for Razor?
\begin{verbatim}
isZero (num 1) + (num 1)
isZero (num 1 + num 1)
isZero (num 2) 3
num 1 + isZero
1 + num 1
true + 1
\end{verbatim}
\end{exe}

\begin{exe}[compulsory]
  Write down the following BNF notations in Agda using \verb$data$ (as we did for \verb$Tm$). \verb$N$ means natural numbers, as before.
\begin{verbatim}
  T ::= op0 | op1 T | op2 T T | op3 T T T | op4 T T T T

  A ::= a | fb B
  B ::= fa A

  V ::= vzero | vsuc V
  E ::= num N | E < E | E = E | var V
  C ::= V := E | while E S | if E then S else S
  S ::= empty | C colon S
\end{verbatim}
\end{exe}

\begin{exe}
  Write a parser for Razor: a program which given a sequence of
  lexical elements, outputs an element of $\mathsf{Tm}$ or an error.
\end{exe}

\begin{exe}[compulsory]
  Which of the following lists of lexical elements are accepted by a parser and produce a \verb$Tm$?
\begin{verbatim}
if true then true else num 0
if true then num 0 else num 0
if num 0 then num 0 else num 0
if num 0 then (num 0 else num 0)
if if then num 0 else num 0
true + false
true + (num 1))
true + (num 1)
(true + isZero)
isZero + num 0
\end{verbatim}
\end{exe}

\begin{exe}[compulsory]
  Which of the following abstract syntax trees are equal to \\
  \verb$num 0 + (num 1 + num 1)$?
\begin{verbatim}
num 0 + ((num 1) + (num 1))
(num 0 + ((num 1) + (num 1)))
(num 0 + num 1) + num 1
((num 0 + num 1) + num 1)
num 1 + num 1
num 2
(num 0 + num 0) + (num 1 + num 1)
ite true (num 0 + (num 1 + num 1)) (num 0)
ite true (num 0 + (num 1 + num 1)) (num 0 + (num 1 + num 1))
ite true (num 0 + (num 1 + num 1)) false
\end{verbatim}
\end{exe}

\subsection{Iteration}

We call a set \verb$A$ with two elements, a ternary operation on
\verb$A$ (an \verb$A → A → A → A$ function), an infinite sequence of
\verb$A$s (a \verb$ℕ → A$ function), an endofunction (an \verb$A → A$
function) and a binary operation on \verb$A$ (an \verb$A → A → A$ function) a \emph{model} of
\emph{RazorAST} (sometimes called a RazorAST algebra). We fix a notation for
this. A RazorAST model (or simply model) is a record with the following fields.
\begin{code}
record Model {ℓ} : Set (lsuc ℓ) where
  field
    Tm      : Set ℓ
    true    : Tm
    false   : Tm
    ite     : Tm → Tm → Tm → Tm
    num     : ℕ → Tm
    isZero  : Tm → Tm
    _+o_    : Tm → Tm → Tm
\end{code}
Note that we used the same names as for the previously defined
trees. We call the above defined Razor programs (trees) the
\emph{syntax} of Razor. The syntax also forms a model, we denote it by
\verb$I$, its components are \verb$I.Tm$, \verb$I.true$,
\verb$I.false$, and so on. The syntax has the property that it can be
interpreted into any other model (it is an initial model, hence the
name \verb$I$): given a model \verb$M$, there is a homomorphism (a
function that commutes with all operators) from \verb$I$ to \verb$M$
which we denote \verb$M.⟦_⟧$. This function is called the
\emph{iterator} (it is sometimes called recursor, fold, catamorphism,
nondependent eliminator, interpreter, evaluator).
\begin{code}
  ⟦_⟧ : I.Tm → Tm
  ⟦ I.true          ⟧ = true
  ⟦ I.false         ⟧ = false
  ⟦ I.ite t t' t''  ⟧ = ite ⟦ t ⟧ ⟦ t' ⟧ ⟦ t'' ⟧
  ⟦ I.num n         ⟧ = num n
  ⟦ I.isZero t      ⟧ = isZero ⟦ t ⟧
  ⟦ t I.+o t'       ⟧ = ⟦ t ⟧ +o ⟦ t' ⟧
\end{code}

The syntax is sometimes called the \emph{free model} over the empty
set: we start with the empty set, and then we freely add elements that
are generated from this set by the operators. In the beginning, the
only generated new elements are \verb$I.true$, \verb$I.false$,
\verb$I.num i$ (for all \verb$i$s), because these don't require any
preexisting elements. Now we already have some elements in the set, so
we can apply the other operators (such as \verb$ite$) to those, which
in turn generate even more elements, then we can apply the operators
to those elements as well, and so on. All the terms in the syntax are
generated this way.

An example of another RazorAST model is \verb$h$ (height) defined as follows.
\begin{code}
H : Model
H = record
  {  Tm      = ℕ
  ;  true    = 0
  ;  false   = 0
  ;  ite     = λ n n' n'' → 1 + max n (max n' n'')
  ;  num     = λ n → 0
  ;  isZero  = λ n → 1 + n
  ;  _+o_    = λ n n' → 1 + max n n'
  }
\end{code}
Note that we distinguish two addition operations:
\verb$+o$ is the addition operator in a model (\verb$H$ in this case), while \verb$+$ is
just addition of (metatheoretic) natural numbers.

If our example term \verb$ite (isZero (zero + suc zero)) false (isZero zero)$
is interpreted in the model \verb$H$, we obtain the height of the tree.
\begin{code}[hide]
module H = Model H
evalH : H.ite (H.isZero (H.num 0 H.+o H.num 1)) H.false (H.isZero (H.num 0)) ≡ 3
evalH =
\end{code}
\begin{code}
  H.ite   (H.isZero (H.num 0 H.+o H.num 1))          H.false (H.isZero (H.num 0))   ≡≡
  1 + max (H.isZero (H.num 0 H.+o H.num 1))    (max  H.false (H.isZero (H.num 0)))  ≡≡
  1 + max (1 + (H.num 0 H.+o H.num 1))         (max  H.false (H.isZero (H.num 0)))  ≡≡
  1 + max (1 + (1 + max (H.num 0) (H.num 1)))  (max  H.false (H.isZero (H.num 0)))  ≡≡
  1 + max (1 + (1 + max 0 0))                  (max  H.false (H.isZero (H.num 0)))  ≡≡
  1 + max (1 + (1 + 0))                        (max  H.false (H.isZero (H.num 0)))  ≡≡
  1 + max 2                                    (max  H.false (H.isZero (H.num 0)))  ≡≡
  1 + max 2                                    (max  0       (H.isZero (H.num 0)))  ≡≡
  1 + max 2                                    (max  0       (1 + (H.num 0)))       ≡≡
  1 + max 2                                    (max  0       (1 + 1))               ≡≡
  1 + max 2                                    (max  0       2)                     ≡≡
  1 + max 2                                    2                                    ≡≡
  1 + 2                                                                             ≡≡
  3                                                                                 ∎
\end{code}

The metatheoretic set of booleans \verb$𝟚$ has two elements \verb$tt$ and \verb$ff$. We denote logical disjunction by \verb$∨$.

We define another model \verb$T$ where terms are elements of \verb$𝟚$ and a term is \verb$tt$ if and only if it contains \verb$true$.
\begin{code}
T : Model
T = record
  {  Tm      = 𝟚
  ;  true    = tt
  ;  false   = ff
  ;  ite     = λ t t' t'' → t ∨ t' ∨ t''
  ;  num     = λ n → ff
  ;  isZero  = λ t → t
  ;  _+o_    = λ t t' → t ∨ t'
  }
\end{code}
Now
\begin{code}[hide]
module T = Model T
evalT : T.ite (T.isZero (T.num 0 T.+o T.num 1)) T.false (T.isZero (T.num 0)) ≡ ff
evalT =
\end{code}
\begin{code}
  T.ite  (T.isZero (T.num 0 T.+o T.num 1))     T.false     (T.isZero (T.num 0))  ≡≡
         (T.isZero (T.num 0 T.+o T.num 1))  ∨  T.false  ∨  (T.isZero (T.num 0))  ≡≡
         (T.num 0  T.+o  T.num 1)           ∨  ff       ∨  (T.num 0)             ≡≡
         (T.num 0  ∨     T.num 1)           ∨  ff       ∨  ff                    ≡≡
         (ff       ∨     ff)                ∨  ff       ∨  ff                    ≡≡
         ff                                                                      ∎
\end{code}
and
\begin{code}[hide]
evalT' : T.ite T.true (T.num 0) T.false ≡ tt
evalT' =
\end{code}
\begin{code}
  T.ite T.true (T.num 0) T.false ≡≡ T.true ∨ (T.num 0) ∨ T.false ≡≡ tt ∨ ff ∨ ff ≡≡ tt
\end{code}
\begin{code}[hide]
  ∎
\end{code}

We have that for any model \verb$M$
\begin{code}[hide]
evalM : ∀{ℓ}{M : Model {ℓ}} → let module M = Model M in
\end{code}
\begin{code}
  M.⟦  I.ite  (I.isZero  (I.num 0  I.+o I.num  1)) I.false  (I.isZero  (I.num 0)) ⟧ ≡
       M.ite  (M.isZero  (M.num 0  M.+o M.num  1)) M.false  (M.isZero  (M.num 0))
\end{code}
\begin{code}[hide]
evalM {M = M} = refl
  where module M = Model M
\end{code}
and similarly for any other syntactic term.

In functional languages like Haskell or Agda, iterating into a
model is a special case of a recursive definition using pattern
matching on the syntax. For example, \verb$H.⟦_⟧$ corresponds to a \verb$height$
function defined by pattern matching as follows.
\begin{AgdaAlign}
\begin{code}
height : I.Tm → ℕ
height I.true            = 0
height I.false           = 0
height (I.ite t t' t'')  = 1 + max (height t) (max (height t') (height t''))
height (I.num n)         = 0
height (I.isZero t)      = 1 + height t
height (t I.+o t')       = 1 + max (height t) (height t')
\end{code}

Iterating into \verb$h$ satisfies the same equations:
\AgdaNoSpaceAroundCode{}
\begin{verbatim}
H.⟦_⟧ : I.Tm → ℕ
\end{verbatim}
\begin{code}[hide]
evalHtrue :
\end{code}
\begin{code}
  H.⟦ I.true ⟧           ≡ 0
\end{code}
\begin{code}[hide]
evalHfalse :
\end{code}
\begin{code}
  H.⟦ I.false ⟧          ≡ 0
\end{code}
\begin{code}[hide]
evalHite : ∀{t t' t''} →
\end{code}
\begin{code}
  H.⟦ I.ite t t' t'' ⟧   ≡ 1 + max H.⟦ t ⟧ (max H.⟦ t' ⟧ H.⟦ t'' ⟧)
\end{code}
\begin{code}[hide]
evalHnum : ∀{n} →
\end{code}
\begin{code}
  H.⟦ I.num n ⟧          ≡ 0
\end{code}
\begin{code}[hide]
evalHisZero : ∀{t} →
\end{code}
\begin{code}
  H.⟦ I.isZero t ⟧       ≡ 1 + H.⟦ t ⟧
\end{code}
\begin{code}[hide]
evalHplus : ∀{t t'} →
\end{code}
\begin{code}
  H.⟦ t I.+o t' ⟧        ≡ 1 + max H.⟦ t ⟧ H.⟦ t' ⟧
\end{code}
\begin{code}[hide]
evalHtrue    = refl
evalHfalse   = refl
evalHite     = refl
evalHnum     = refl
evalHisZero  = refl
evalHplus    = refl
\end{code}
\end{AgdaAlign}
\AgdaSpaceAroundCode{}

Some Haskell functions defined by pattern matching are not expressible
using iteration into a model. Haskell allows nonterminating
recursion or recursion where some cases are not handled, as in the
following examples.
\begin{verbatim}
f : I.Tm → ℕ
f t = f t

g : I.Tm → ℕ
g I.true  = 3
g I.false = 1
\end{verbatim}
In Agda, all functions defined by pattern matching are also expressible
using the iterator (or using induction, see below). For details see
\cite{conorthesis,andreasfoetus}.

The syntactic operators are \emph{disjoint}: for example,
\verb$I.true$ is not equal to \verb$I.false$. We can show this using
a model where terms are metatheoretic booleans, \verb$true$ is metatheoretic true, \verb$false$ is
metatheoretic false. The other components don't matter, here we just
set them to constant false.
\begin{code}
TF : Model
TF = record
  {  Tm      = 𝟚
  ;  true    = tt
  ;  false   = ff
  ;  ite     = λ _ _ _ → ff
  ;  num     = λ _ → ff
  ;  isZero  = λ _ → ff
  ;  _+o_    = λ _ _ → ff
  }
\end{code}
\begin{code}[hide]
module TF = Model TF
\end{code}
Now we can use the iterator and \verb$congruence$ of equality to
obtain a contradiction from \verb$I.true ≡ I.false$:
\begin{code}
true≠false : ¬ (I.true ≡ I.false)
true≠false e = tt≠ff (cong TF.⟦_⟧ e)
\end{code}

However, there are models where \verb$true = false$, e.g.\ the
trivial model where terms are given by the set with one element
\verb$tt$ and all operators return this element.
\begin{code}
Triv : Model
Triv = record
  {  Tm      = Lift ⊤
  ;  true    = _
  ;  false   = _
  ;  ite     = _
  ;  num     = _
  ;  isZero  = _
  ;  _+o_    = _
  }
\end{code}

Every syntactic term is \emph{finite}, e.g.\ there is no syntactic term of
the form \\ \verb$I.isZero (I.isZero (I.isZero ⋯))$ (an infinitely
deep tree with \verb$I.isZero$ at each node) because it would be
mapped to an infinite natural number by \verb$H.⟦_⟧$ which does not
exist. This is not true for arbitrary models: there can be models
where \verb$Tm$ has infinite elements, for example, \verb$Tm = ℕ → 𝟚$
(a term is an infinite sequence of booleans).

\begin{exe}[compulsory]\label{exe:razor-trues}
  Define a model where a term is a natural number and if we interpret a syntactic term in the model,
  we get the number of \verb$true$s in the tree. For example, \verb$false +o num 3 = 0$,
  \verb$true +o num 3 = 1$, \verb$true +o true = 2$.
\end{exe}

\begin{exe}[compulsory]\label{exe:razor-size}
  Define a model which calculates the number of nodes in a tree, e.g.\
  \verb$num 1 = 1$, \verb$isZero (num 1) = 2$,
  \verb$isZero (num 1) + true = 4$.
\end{exe}

\begin{exe}[compulsory]
  Prove that \verb$I.num 0 I.+o I.num 0$ is not equal \verb$I.num 0$.
\end{exe}

\begin{exe}[compulsory]
  Prove that \verb$I.isZero (I.num 100)$ is not equal \verb$I.isZero I.true$.
\end{exe}

\begin{exe}[compulsory]
  Prove that \verb$I.isZero (I.num 100)$ is not equal \verb$I.isZero (I.num 101)$.
\end{exe}

\begin{exe}
  Create a model where \verb$true = false$, but \verb$true ≠ num 0$.
\end{exe}

\begin{exe}
  Define a RazorAST model where terms are \verb$ℕ → 𝟚$
  sequences, any sequence that starts with \verb$tt$ is interpreted as
  \verb$true$, any sequence that startsf with \verb$ff$ is
  \verb$false$, \verb$num i$ is a sequence with \verb$i$ many
  \verb$tt$s in it. Addition is a sequence where the number of
  \verb$tt$s is the sum of the number of \verb$tt$s in the two
  sequences.
\end{exe}

\begin{exe}\label{ex:cstyle}
Define a RazorAST model where terms are natural numbers, booleans
are interpreted in C-style: false is $0$, true is $1$ and for
if-then-else, anything that is not $0$ is interpreted as true. We can call
this model the degenerate standard model.
\end{exe}

\begin{exe}[recommended]
Define a nonstandard C-style model the interpretation into which is not onto. What is the simplest such model?
\end{exe}

\begin{exe}[compulsory]
  Is there a model where \verb$Tm = Lift ⊥$?
\end{exe}

\begin{exe}[compulsory]
Show that for any two models \verb$M$ and \verb$N$ there is a model
where \verb$Tm = M.Tm × N.Tm$.
\end{exe}

\begin{exe}
  Create a model where \verb$Tm = 𝟚$, \verb$num 0 = tt$ and all other operators are
  \verb$ff$. With the help of this, create a function \verb$isZero : I.Tm → 𝟚$. Then
  create an optimisation \verb$I.Tm → I.Tm$ which maps \verb$I.num 0 + t$ to
  \verb$t$ and \verb$t + I.num 0$ to \verb$t$.
\end{exe}

\begin{exe}[compulsory]
  Consider a subset of RazorAST where we only have one type:
  \begin{verbatim}
    Tm : Set
    zero : Tm
    suc : Tm → Tm
    _+_ : Tm → Tm → Tm
  \end{verbatim}
  Define a model \verb$St$ such that \verb$St.⟦_⟧ : I.Tm → ℕ$ is an
  interpreter for this language (where \verb$I$ is the syntax for this language).
  E.g.\ \verb$St.⟦num 1 + num 3⟧ = 4$.
\end{exe}

\subsection{Induction}
\label{sec:razor-ast-ind}

In addition to iteration, the syntax supports induction which is a
generalisation (dependent variant) of iteration. Induction can be
stated by saying that for any \emph{dependent model} \verb$D$ there
is a \emph{dependent homomorphism} from \verb$I$ to \verb$D$. A
\emph{dependent model} (dependent algebra, displayed algebra/model) is
given by the following components.
\begin{code}
record DepModel {ℓ} : Set (lsuc ℓ) where
  field
    Tm∙      : I.Tm → Set ℓ
    true∙    : Tm∙ I.true
    false∙   : Tm∙ I.false
    ite∙     : {t : I.Tm} → Tm∙ t → {u : I.Tm} → Tm∙ u → {v : I.Tm} → Tm∙ v →
               Tm∙ (I.ite t u v)
    num∙     : (n : ℕ) → Tm∙ (I.num n)
    isZero∙  : {t : I.Tm} → Tm∙ t → Tm∙ (I.isZero t)
    _+o∙_    : {u : I.Tm} → Tm∙ u → {v : I.Tm} → Tm∙ v → Tm∙ (u I.+o v)
\end{code}
In a dependent model, instead of a set of terms, there is a family
of sets indexed over \verb$I.Tm$, that is, there is a set \verb$Tm∙ t$
for each element \verb$t : I.Tm$ (See Figure \ref{fig:depmodel}). Then we have elements of these
families at each syntactic operator as index. So, we have a \verb$Tm∙ I.true$, a
\verb$Tm∙ I.false$, $\dots$, a \verb$Tm∙ (t I.+o t')$. For
operators with parameters, we also have induction hypotheses, for
example, we have \verb$Tm∙ t$ and \verb$Tm∙ t'$ as inputs for \verb$_+o_$.

\begin{figure}
\begin{center}
\begin{tikzpicture}
\draw (0,1) circle (0.9cm);
\draw (2,1) circle (0.9cm);
\draw (4,1) circle (0.9cm);
\draw (6,1) circle (0.9cm);
\node (d1) at (0,2.25) {\verb$D.Tm t$};
\node (d2) at (2,2.25) {\verb$D.Tm t'$};
\node (d3) at (4,2.25) {\verb$D.Tm (t I.+o t')$};
\node (d4) at (6,2.25) {\verb$D.Tm I.true$};
\draw[rounded corners=12pt] (-1,-1) rectangle ++(10,0.9);
\node (i) at (-1.5,-0.5) {\verb$I.Tm$};
\node (i1) at (0,-0.5) {\verb$t$};
\node (i2) at (2,-0.5) {\verb$t'$};
\node (i3) at (4,-0.5) {\verb$(t I.+o t')$};
\node (i4) at (6,-0.5) {\verb$I.true$};
\node (i4) at (8,-0.5) {$\dots$};
\node (d5) at (0,1) {\verb$u$};
\node (d6) at (2,1) {\verb$u'$};
\node (d7) at (4,1) {\verb$(u D.+o u')$};
\node (d8) at (6,1) {\verb$D.true$};
\node (d8) at (8,1) {$\dots$};
\end{tikzpicture}
\end{center}
\cprotect\caption{Depiction of a dependent model \verb$D$.
There is a separate set \verb$D.Tm t$ for every
syntactic term \verb$t$.}
\label{fig:depmodel}
\end{figure}

The dependent homomorphism from the syntax is called \emph{induction}
(induction principle, eliminator). This is a dependent function
which for an input \verb$t : I.Tm$ outputs a \verb$Tm∙ t$. Moreover, as in
the non-dependent case, it maps each syntactic operator to its
counterpart in the dependent model.
\begin{code}
  ⟦_⟧ : (t : I.Tm) → Tm∙ t
  ⟦ I.true          ⟧ = true∙
  ⟦ I.false         ⟧ = false∙
  ⟦ I.ite t t' t''  ⟧ = ite∙ ⟦ t ⟧ ⟦ t' ⟧ ⟦ t'' ⟧
  ⟦ I.num n         ⟧ = num∙ n
  ⟦ I.isZero t      ⟧ = isZero∙ ⟦ t ⟧
  ⟦ t I.+o t'       ⟧ = ⟦ t ⟧ +o∙ ⟦ t' ⟧
\end{code}

A special case of the dependent model is when \verb$Tm∙ t = Lift (P t)$
for some \verb$P : I.Tm → Prop$, that is, \verb$Tm$ is a predicate
(unary relation) on syntactic terms. In this case, the other
components say that each syntactic operator respects the
predicate. For example, if the predicate holds for \verb$t$ and
\verb$t'$, then it also holds for \verb$t I.+o t'$. C.f.\ natural
number models (a set with an element and an endofunction) and
induction on natural numbers, see Section \ref{sec:natural}. All
inductively defined sets come with a notion of model, iteration,
dependent model and induction \cite{popl19}. In addition to natural
numbers, other well-known examples are lists, binary trees.

Consider the following model which describes the number of leaves.
\begin{code}
L1 : Model
L1 = record
  { Tm     = ℕ
  ; true   = 1
  ; false  = 1
  ; ite    = λ t t' t'' → t + t' + t''
  ; num    = λ _ → 1
  ; isZero = λ t → t
  ; _+o_   = _+_
  }
module L1 = Model L1
\end{code}
Here is another model for describing the number of leaves using a different logic: At a binary branching, the number of leaves increases by one, at a ternary branching it increases by two.
\begin{code}
L2 : Model
L2 = record
  { Tm     = ℕ
  ; true   = 0
  ; false  = 0
  ; ite    = λ t t' t'' → 2 + t + t' + t''
  ; num    = λ _ → 0
  ; isZero = λ t → t
  ; _+o_   = λ t t' → 1 + t + t'
  }
module L2 = Model L2
\end{code}
Now we prove that counting the leaves of a syntactic term using
\verb$L1$ is equal to counting the leaves using \verb$L2$ and adding
one. To this end, we define the following dependent model
\begin{code}
D : DepModel
D = record
  { Tm∙ = λ t → Lift (L1.⟦ t ⟧ ≡ 1 + L2.⟦ t ⟧)
  ; true∙ = mk refl
  ; false∙ = mk refl
  ; ite∙ = λ { {t}(mk t∙){u}(mk u∙){v}(mk v∙) → mk (
    L1.⟦ t I.+o u I.+o v ⟧ 
                                      ≡⟨ refl ⟩
    L1.⟦ t ⟧ + L1.⟦ u ⟧ + L1.⟦ v ⟧ 
                                      ≡⟨ cong₃ (λ x y z → x + y + z) t∙ u∙ v∙ ⟩
    (1 + L2.⟦ t ⟧) + (1 + L2.⟦ u ⟧) + (1 + L2.⟦ v ⟧)
                                      ≡⟨ ass+ {1 + L2.⟦ t ⟧} ⟩
    (1 + L2.⟦ t ⟧) + ((1 + L2.⟦ u ⟧) + (1 + L2.⟦ v ⟧))
                                      ≡⟨ cong ((1 + L2.⟦ t ⟧) +_) (ass+ {1 + L2.⟦ u ⟧} ⁻¹) ⟩
    (1 + L2.⟦ t ⟧) + ((1 + L2.⟦ u ⟧ + 1) + L2.⟦ v ⟧)
                                      ≡⟨ cong  (λ z → (1 + L2.⟦ t ⟧) + (z + L2.⟦ v ⟧))
                                               (+comm {1 + L2.⟦ u ⟧}) ⟩
    (1 + L2.⟦ t ⟧) + (2 + L2.⟦ u ⟧ + L2.⟦ v ⟧)
                                      ≡⟨ refl ⟩
    (1 + L2.⟦ t ⟧) + (2 + (L2.⟦ u ⟧ + L2.⟦ v ⟧))
                                      ≡⟨ ass+ {1 + L2.⟦ t ⟧} ⁻¹ ⟩
    ((1 + L2.⟦ t ⟧) + 2) + (L2.⟦ u ⟧ + L2.⟦ v ⟧)
                                      ≡⟨ cong  (_+ (L2.⟦ u ⟧ + L2.⟦ v ⟧))
                                               (+comm {1 + L2.⟦ t ⟧}{2}) ⟩
    3 + L2.⟦ t ⟧ + (L2.⟦ u ⟧ + L2.⟦ v ⟧)
                                      ≡⟨ ass+ {3 + L2.⟦ t ⟧} ⁻¹ ⟩
    3 + L2.⟦ t ⟧ + L2.⟦ u ⟧ + L2.⟦ v ⟧
                                      ≡⟨ refl ⟩
    1 + L2.⟦ I.ite t u v ⟧
                                      ∎)}
  ; num∙ = λ _ → mk refl
  ; isZero∙ = λ t∙ → t∙
  ; _+o∙_ = λ { {u}(mk u∙){v}(mk v∙) → mk (
    L1.⟦ u I.+o v ⟧
                                      ≡⟨ refl ⟩
    L1.⟦ u ⟧ + L1.⟦ v ⟧
                                      ≡⟨ cong (_+ L1.⟦ v ⟧) u∙  ⟩
    1 + L2.⟦ u ⟧ + L1.⟦ v ⟧
                                      ≡⟨ cong (λ z → 1 + L2.⟦ u ⟧ + z) v∙ ⟩
    (1 + L2.⟦ u ⟧) + (1 + L2.⟦ v ⟧)
                                      ≡⟨ ass+ {1 + L2.⟦ u ⟧} ⁻¹ ⟩
    ((1 + L2.⟦ u ⟧) + 1) + L2.⟦ v ⟧
                                      ≡⟨ cong (_+ L2.⟦ v ⟧) (ass+ {1}{_}{1} ⁻¹) ⟩
    (1 + (L2.⟦ u ⟧ + 1)) + L2.⟦ v ⟧
                                      ≡⟨ cong  (λ z → 1 + z + L2.⟦ v ⟧)
                                               (+comm {L2.⟦ u ⟧}{1}) ⟩
    (1 + (1 + L2.⟦ u ⟧)) + L2.⟦ v ⟧
                                      ≡⟨ refl ⟩
    2 + (L2.⟦ u ⟧ + L2.⟦ v ⟧)
                                      ≡⟨ refl ⟩
    1 + (L2.⟦ u I.+o v ⟧)
                                      ∎)}
  }
module D = DepModel D
\end{code}
Interpreting into the dependent model \verb$D$ gives our proof:
\begin{code}
L1=L2 : ∀ t → L1.⟦ t ⟧ ≡ 1 + L2.⟦ t ⟧
L1=L2 t = un D.⟦ t ⟧
\end{code}

The operators of the syntax are \emph{injective}. For example, if
\verb$I.isZero t ≡ I.isZero t'$, then \verb$t ≡ t'$. To show this, we
use a trivial dependent model which is only used to peel off the
\verb$I.isZero$ from any term.
\begin{code}
module inj where
  D' : DepModel
  D' = record
    { Tm∙ = λ _ → I.Tm
    ; true∙ = I.true
    ; false∙ = I.true
    ; ite∙ = λ _ _ _ → I.true
    ; num∙ = λ _ → I.true
    ; isZero∙ = λ {t} _ → t
    ; _+o∙_ = λ _ _ → I.true
    }
  module D' = DepModel D'
  isZeroInj : ∀{t t'} → I.isZero t ≡ I.isZero t' → t ≡ t'
  isZeroInj e = cong D'.⟦_⟧ e
\end{code}
Note that there are models in which \verb$isZero$ is not injective.

\begin{exe}[recommended]
Show that the number of \verb$true$s in a syntactic term is less than
or equal to \verb$3$ to the power the height of the tree. For this,
define a dependent model \verb$D$ where \verb$D.Tm t$ has an
inhabitant exactly when \verb$N.⟦t⟧$ is less than or equal to \verb$3 ^ (H.⟦t⟧)$.
Here \verb$N$ is the model defined in Exercise
\ref{exe:razor-trues} and \verb$H$ is the model defined for
calculating the height of a term.
% \begin{code}[hide]
% import Lemmas
%
% D-1 : {t : I.Tm} →
%   ↑p (T.⟦ t ⟧ ≤ 3 ^ℕ H.⟦ t ⟧) →
%   ↑p (T.⟦ I.suc t ⟧ ≤ 3 ^ℕ H.⟦ I.suc t ⟧)
% D-1 le = ↑[ Lemmas.≤-+ℕ-r ↓[ le ]↓ ]↑
%
% D-2 : {t t' : I.Tm} →
%   ↑p (T.⟦ t ⟧ ≤ 3 ^ℕ H.⟦ t ⟧) →
%   ↑p (T.⟦ t' ⟧ ≤ 3 ^ℕ H.⟦ t' ⟧) →
%   ↑p (T.⟦ t I.+ t' ⟧ ≤ 3 ^ℕ H.⟦ t I.+ t' ⟧)
% D-2 {t} {t'} le1 le2 = ↑[
%       (Lemmas.+ℕ-≤-mono ↓[ le1 ]↓ ↓[ le2 ]↓)
%     Lemmas.≤-◾
%       Lemmas.≤-+ℕ-l {c = 3 ^ℕ max H.⟦ t ⟧ H.⟦ t' ⟧}
%         (Lemmas.+ℕ-≤-mono
%           (Lemmas.^ℕ-≤-mono-r {b = H.⟦ t ⟧} (s≤s z≤n) Lemmas.≤-max-l)
%           (Lemmas.≤-+ℕ-r
%             (Lemmas.^ℕ-≤-mono-r
%               {b = H.⟦ t' ⟧} {b' = max H.⟦ t ⟧ H.⟦ t' ⟧}
%               (s≤s z≤n) Lemmas.≤-max-r
%             )
%           )
%         )
%   ]↑
%
% D-3 : {t t' t'' : I.Tm} →
%   ↑p (T.⟦ t ⟧ ≤ 3 ^ℕ H.⟦ t ⟧) →
%   ↑p (T.⟦ t' ⟧ ≤ 3 ^ℕ H.⟦ t' ⟧) →
%   ↑p (T.⟦ t'' ⟧ ≤ 3 ^ℕ H.⟦ t'' ⟧) →
%   ↑p (T.⟦ I.ite t t' t'' ⟧ ≤ 3 ^ℕ H.⟦ I.ite t t' t'' ⟧)
% D-3 {t} {t'} {t''} le1 le2 le3 = ↑[
%       Lemmas.+ℕ-≤-mono (Lemmas.+ℕ-≤-mono ↓[ le1 ]↓ ↓[ le2 ]↓) ↓[ le3 ]↓
%     Lemmas.≤-◾
%       Lemmas.+ℕ-≤-mono
%         {a = 3 ^ℕ H.⟦ t ⟧ +ℕ 3 ^ℕ H.⟦ t' ⟧}
%         {b = 3 ^ℕ H.⟦ t'' ⟧}
%         {b' = 3 ^ℕ max H.⟦ t ⟧ (max H.⟦ t' ⟧ H.⟦ t'' ⟧)}
%         (Lemmas.+ℕ-≤-mono
%           {a = 3 ^ℕ H.⟦ t ⟧}
%           {a' = 3 ^ℕ max H.⟦ t ⟧ (max H.⟦ t' ⟧ H.⟦ t'' ⟧)}
%           (Lemmas.^ℕ-≤-mono-r
%             {b = H.⟦ t ⟧}
%             {b' = max H.⟦ t ⟧ (max H.⟦ t' ⟧ H.⟦ t'' ⟧)}
%             (s≤s z≤n) (Lemmas.≤-max-3a {b = H.⟦ t' ⟧})
%           )
%           (Lemmas.≤-+ℕ-r
%             {b = 3 ^ℕ max H.⟦ t ⟧ (max H.⟦ t' ⟧ H.⟦ t'' ⟧)}
%             (Lemmas.^ℕ-≤-mono-r {b = H.⟦ t' ⟧} (s≤s z≤n) (Lemmas.≤-max-3b {a = H.⟦ t ⟧}))
%           )
%         )
%         (Lemmas.^ℕ-≤-mono-r
%           {b = H.⟦ t'' ⟧}
%           -- {b' = max H.⟦ t ⟧ (max H.⟦ t' ⟧ H.⟦ t'' ⟧)}
%           (s≤s z≤n) (Lemmas.≤-max-3c {a = H.⟦ t ⟧})
%         )
%     Lemmas.≤-◾
%       Lemmas.≤-≡ (Lemmas.+ℕ-comm {b = 3 ^ℕ max H.⟦ t ⟧ (max H.⟦ t' ⟧ H.⟦ t'' ⟧)})
%   ]↑
% \end{code}
% \begin{code}
% D : DepModel
% D = record
%   { Tm      = λ t → ↑p (T.⟦ t ⟧ ≤ 3 ^ℕ H.⟦ t ⟧)
%   ; true    = ↑[ s≤s z≤n ]↑
%   ; false   = ↑[ z≤n ]↑
%   ; ite     = λ {t}{t'}{t''} → D-3 {t}{t'}{t''}
%   ; zero    = ↑[ z≤n ]↑
%   ; suc     = λ {t} → D-1 {t}
%   ; isZero  = λ {t} → D-1 {t}
%   ; _+_     = λ {t}{t'} → D-2 {t}{t'}
%   }
% \end{code}
\begin{verbatim}
D.Tm t := N.⟦ t ⟧ ≤ 3 ^ (H.⟦ t ⟧)
D.true : N.⟦ I.true ⟧ = 1 ≤ 1 = 3 ^ 0 = 3 ^ (H.⟦ I.true ⟧)
D.false : N.⟦ I.false ⟧ = 0 ≤ 1 = 3 ^ 0 = 3 ^ (H.⟦ I.false ⟧)
D.ite tᴰ tᴰ' tᴰ'' :
  N.⟦ I.ite t t' t'' ⟧ =
  N.⟦t⟧ + N.⟦t'⟧ + N.⟦t''⟧ ≤(tᴰ,tᴰ',tᴰ'')
  3 ^ (H.⟦t⟧) + 3 ^ (H.⟦t'⟧) + 3 ^ (H.⟦t''⟧) ≤
  3 ^ (H.⟦t⟧) + 3 ^ (H.⟦t'⟧) + 3 ^ (H.⟦t''⟧) ≤
  3 * 3 ^ (max H.⟦t⟧ (max H.⟦t'⟧ H.⟦t''⟧)) =
  3 ^ (1 + max H.⟦t⟧ (max H.⟦t'⟧ H.⟦t''⟧)) =
  3 ^ (H.⟦ I.ite t t' t'' ⟧)
D.num n : N.⟦ I.num n ⟧ = 0 ≤ 1 = 3 ^ 0 = 3 ^ (H.⟦ I.num n ⟧)
D.isZero tᴰ : N.⟦ I.isZero t ⟧ = N.⟦ t ⟧ ≤(tᴰ) 3 ^ (H.⟦ t ⟧) ≤ 3 ^ (1 + H.⟦ t ⟧) = 3 ^ (H.⟦ I.isZero t ⟧)
tᴰ D.+o tᴰ' :
  N.⟦ t I.+o t' ⟧ =
  N.⟦ t ⟧ + N.⟦ t' ⟧ ≤(tᴰ,tᴰ')
  3 ^ (H.⟦ t ⟧) + 3 ^ (H.⟦ t' ⟧) ≤
  2 * 3 ^ (max H.⟦ t ⟧ H.⟦ t' ⟧) ≤
  3 * 3 ^ (max H.⟦ t ⟧ H.⟦ t' ⟧) ≤
  3 ^ (1 + max H.⟦ t ⟧ H.⟦ t' ⟧) =
  3 ^ (H.⟦ t I.+o t' ⟧)
\end{verbatim}
\end{exe}

\begin{exe}
  Show that every model can be turned into a dependent model, and
  derive the iterator using the induction principle.
\end{exe}

\begin{exe}[recommended]
  Prove that \verb$H.⟦ t ⟧ ≤ S.⟦ t ⟧$ where \verb$S$ is the model defined in
  exercise \ref{exe:razor-size}.
\end{exe}

\begin{exe}[recommended]
  Prove that \verb$I._+o_$ is injective: if \verb$u I.+o v ≡ u' I.+o v'$, then \verb$u ≡ u'$
  and \verb$v = v'$.
  Define a model \verb$M$ where \verb$M._+o_$ is not injective.
\end{exe}

\begin{exe}
Define a model which counts the number of \verb$true$s and \verb$false$s in a term.
Define a model which counts the number of \verb$true$s in a term. Show
that interpreting a syntactic term in the first one always gives a greater
or equal number than interpreting a term in the second one.
\end{exe}
