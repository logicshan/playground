Posted by Jesper on November 4, 2021

As a compiler developer or programming language researcher, one very common question is how to represent the syntax of a programming language in order to interpret, compile, analyze, optimize, and/or transform it.

One of the first lessons you learn is to not represent syntax as the literal string of characters written by the programmer, but rather convert it to an _abstract syntax tree_ (AST). This has a number of advantages: it enforces structure on programs, makes the syntax easier to traverse and transform, erases irrelevant details (e.g. whitespace and comments), and allows for better separation of different intermediate states of the syntax.

However, syntax is in fact not a tree but a _graph_: names (of variables, functions, classes, modules, …) can point to potentially far-away locations in the program’s text. The way these work is that one occurrence of the name _binds_ the name (aka the binder), and other occurrences of the same name _mention_ the name, thus pointing to the binder.

Just as representing syntax as a string is not a good idea for most purposes, representing names as strings is usually not a good idea either. This will be clear to anyone who has ever implemented capture-avoiding substitution for lambda-terms with strings as variable names (and if you haven’t, I invite you to do so). Hence we would like to have a generic and universal way to represent the structure of binders-and-mentions, similar to how abstract syntax trees represent the structure of syntactical-constructs-and-their-components.

Unfortunately, in contrast to the case of abstract syntax, there are countless different techniques, frameworks, and meta-languages for dealing with name binding, none of which come close to be universally accepted or clearly superior to the others. For the compiler developer or PL researcher who just wants to define their syntax and move on to more interesting things, this is frustrating, to say the least. Make the wrong choice, and you are stuck with impossibly complex and buggy code for manipulating variables, or proving an endless stream of substitution lemmas, or figuring out too late that the thing you want to do is just not possible with the chosen representation of names.

In this post, I will give an overview of all the different techniques for implementing syntax with binders in Agda that I could find. With each technique, I will show how to use it in Agda to represent the syntax of (untyped) lambda calculus, and also explain briefly what the main motivation is for using it. I hope this will be useful to you for making an informed choice between these options.

Since there’s quite a few of them, I can only give a brief description of each representation in this post. If you want to learn more about any of them, you can find my full list of references [on Researchr](https://researchr.org/bibliography/variable-binding/publications). Also, since this is a blog post and not a book, I will limit this overview to representations that can be defined and used in Agda or a similar dependently-typed functional language (e.g. Coq or Haskell), not in language features that could be added to Agda or in entire new languages built for this specific purpose. In particular, this means representations that require a (meta-)language with a built-in way to assign unique identifiers are ruled out.

Finally, in this post I will not consider the problem of _name resolution_, i.e. how to figure out which binder each occurrence of a name points to. Instead, I focus on how to represent and manipulate syntax where names are used correctly according to the rules of the language. You can think of this as finding a good representation of the _output_ of name resolution, similar to how an AST is the output of parsing.

With these disclaimers in place, it is time to start with the first and possibly most ubiqitous representation: de Bruijn indices.

## De Bruijn indices

[De Bruijn indices](https://www.win.tue.nl/automath/archive/pdf/aut029.pdf) are the most common _nameless_ representation of name binding. A de Bruijn index represents a name by counting how many binders need to be skipped when traversing upwards through the AST before one reaches the name’s binding site.

Here is the definition of lambda terms using de Bruijn indices, and a representation of the term `λ f. λ x. f x`:

```
module DeBruijnSyntax where
  data Term : Set where
    var : ℕ → Term
    lam : Term → Term
    app : Term → Term → Term

  ex : Term
  ex = lam {-f-} (lam {-x-} (app (var {-f-} 1) (var {-x-} 0)))

```

De Bruijn syntax is used widely in the implementation and formalization of programming languages, especially with functional implementation languages. For example, Agda is implemented in Haskell and the internal syntax represents variables (but not other names) using de Bruijn indices.

The big advantage of de Bruijn syntax is that each lambda-expression has a _unique_ representation and hence any two α-equivalent terms (e.g. `λ x. x` and `λ y. y`) are represented the same. It also leads to a more uniform and - arguably - more pleasant implementation of substitution than on syntax with strings for names. On the other hand, it is often quoted as a good “reverse Turing test” because most humans have a hard time grasping the meaning of a term and reasoning about them correctly.

A variation on de Bruijn indices are de Bruijn _levels_, which count the number of binders starting from the root node rather than from the occurrence of the name. This simplifies the implementation of some operations, but the assumption there exists a global ‘root node’ complicates others, so overall the choice between de Bruijn indices and levels is kind of a wash.

## Locally nameless

One of the main problems with de Bruijn syntax is the absence of any actual names when constructing syntax. One possible solution is to distinguish between variables that are _bound_ and those that are _free_, and note that only bound variables need to be anonymous. This leads to the class of syntax representations known as [_locally nameless_](http://www.chargueraud.org/research/2009/ln/main.pdf).

```
module LocallyNameless where

  Name = String

  data Term : Set where
    bound : ℕ → Term
    free  : Name → Term
    lam   : Term → Term
    app   : Term → Term → Term

```

To mediate between bound and free variables (e.g. when going under a binder), we define operations for _opening_ and _closing_ a term:

```
  openUnder : ℕ → Name → Term → Term
  openUnder k x (bound n) =
    if does (k ℕ.≟ n) then free x else bound n
  openUnder k x (free y)  = free y
  openUnder k x (lam u)   = lam (openUnder (suc k) x u)
  openUnder k x (app u v) =
    app (openUnder k x u) (openUnder k x v)

  openT = openUnder 0

  closeUnder : ℕ → Name → Term → Term
  closeUnder k x (bound n) = bound n
  closeUnder k x (free y)  =
    if does (x String.≟ y) then bound k else free y
  closeUnder k x (lam u)   = lam (closeUnder (suc k) x u)
  closeUnder k x (app u v) =
    app (closeUnder k x u) (closeUnder k x v)

  closeT = closeUnder 0

```

Using `closeT`, we can write down variables as strings but convert them to de Bruijn indices on the fly:

```
  ex = lam (closeT "f" (
         lam (closeT "x" (
           app (free "f") (free "x")
         ))
       ))

  _ : ex ≡ lam (lam (app (bound 1) (bound 0)))
  _ = refl


```

There are many possible variants of the locally nameless style, where either the representation of either free or bound variables differs. For example, representing both free and bound variables as names (from two distinct types) leads to the [_locally named_](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.53.2065&rep=rep1&type=pdf) representation, which was actually introduced first. In the other direction, instead of representing free variables as strings one could instead represent them as de Bruijn levels, which results in an interesting combination of de Bruijn indices and de Bruijn levels.

Locally nameless syntax representations have been successfully used for doing formal metatheory in Coq, including the formalization of PCUIC for the [MetaCoq project](https://github.com/MetaCoq/metacoq/blob/coq-8.11/pcuic/theories/PCUICAst.v). However, using it successfully requires a lot of boilerplate for dealing with opening and closing of terms, which might be prohibiting unless the boilerplate can be generated automatically. Repeated opening and closing of terms might also introduce a performance bottleneck when this approach is used for a practical implementation and not just doing metatheory.

## Nominal signatures

Next to the broad family of nameless representations based on de Bruijn’s representation, a wholly different way to think about names is by relying on [_nominal techniques_](http://dx.doi.org/10.1016/j.tcs.2004.06.016). Very briefly speaking, this means we rely on the presence of one or more abstract sorts of _atoms_ (i.e. names) together with an operation for swapping two atoms in a term and a predicate expressing freshness of an atom with respect to a term. On top of these, one can define a sort constructor for abstracting over a single atom/name (I am deliberately using the word ‘sort’ instead of ‘type’ since these are not regular Agda types). We can then use name abstraction directly to write down a signature of our syntax and its induction principle.

While nominal techniques provide a general approach to define and reason about syntax with binders, I actually hesitate to include it here because it seems to require special language support to use effectively, which Agda does not have. However, we can work around that problem by defining a record type that specifies an abstract interface for working with atoms and (nominal) sorts (here I simplify it to a single sort of atoms):

```
module Nominal where
  record Nominal : Set₂ where
    field
      Sort  : Set₁
      Atom  : Sort
      1ᵉ    : Sort
      _×ᵉ_  : Sort → Sort → Sort
      _→ᵉ_  : Sort → Sort → Set
      absᵉ  : Sort → Sort
      -- lots of axioms omitted
  open Nominal {{...}}

```

The interface first declares a type `Sort` of sorts, and a particular sort `Atom` of atoms. It also contains fields for the analogues of regular Agda type constructors on sorts, such as pairs, functions, and predicates. We then declare that for each sort `A`, we have another sort `absᵉ A` of elements of `A` abstracted over a single (unknown) name. Finally, although I didn’t write them here, if you would actually want to use this you would also need lots of other fields with axioms to specify freshness, as well as how to instantiate an element of `absᵉ A` with a fresh variable.

Once we have declared this abstract interface, we can use it to declare our syntax. Since Agda does not allow defining datatypes in an abstract type such as `Sort`, we once again resort to an abstract interface for declaring the syntax.

```
  module _ {{_ : Nominal}} where
    record Syntax : Set₁ where
      field
        Term : Sort
        var  : Atom →ᵉ Term
        app  : (Term ×ᵉ Term) →ᵉ Term
        lam  : (absᵉ Term) →ᵉ Term
        -- induction principle omitted

```

Since these interfaces are abstract, an important question is whether it is actually possible to implement them - otherwise they’d be pretty useless. The traditional way to do this relies on the presence of _nominal sets_ - sets with built-in operations for swapping and freshness - for which I am not sure how easy they are to define in Agda. Luckily, we don’t have to, as there is an easier way to implement the `Nominal` and `Syntax` interfaces in terms of the “Namely, Painless” approach by Nicolas Pouillard (see the section on it further down below).

## Higher-order abstract syntax

Instead of trying to find a good encoding of variables for our syntax, it is tempting to instead try to re-use the existing variable binding capabilities of our meta-language (Agda). This third approach (after nameless and nominal techniques) is known as [_higher-order abstract syntax_](https://dl.acm.org/doi/pdf/10.1145/960116.54010). A naive attempt at using this in Agda goes as follows:

```
module ‶HOAS″ where
  {-# NO_POSITIVITY_CHECK #-}
  data Term : Set where
    lam : (Term → Term) → Term
    app : Term → Term → Term

  ex : Term
  ex = lam (λ f → lam (λ x → app f x))

```

There is no explicit case for variables in the syntax, instead variables are meta-level variables of type `Term`. The scoping discipline of the meta-language thus enforces that variables cannot be used outside of their scope, i.e. terms are well-scoped by construction. In addition, we get the nice property of de Bruijn syntax that any two α-equivalent terms are equal. Moreover, substitution can be implemented simply by function application on the meta-level.

But (and this is a very big but) this approach does not actually work. First of all, this type of terms is not strictly positive (as indicated by the big `NO_POSITIVITY_CHECK` pragma on top) and can in fact easily be exploited to define a non-normalizing term, thus breaking Agda’s termination guarantees. Another huge problem is that it is not possible to match on a term to see if it is a variable, so many algorithms on the syntax (such as checking syntactic equality) are simply impossible to implement. In addition, this representation allows defining so-called ‘exotic terms’ that pattern match on the syntactic structure of a variable, which should not be possible in the syntax of our language:

```
  exotic : Term
  exotic = lam (λ x → case x of λ where
                        (lam _)   → x
                        (app _ _) → lam (λ y → y))

```

Because of all these problems, most people would not consider this type to be ‘real’ HOAS, and instead reserve the term for languages that actually support a weak function space, such as [Twelf](http://www.twelf.org/), [Beluga](http://complogic.cs.mcgill.ca/beluga/), or [Dedukti](https://deducteam.github.io/).

A variant of HOAS that _can_ be used effectively in a language without a weak function space is [_parametric higher-order abstract syntax_](http://doi.acm.org/10.1145/1411204.1411226) (PHOAS). Instead of representing variables directly as meta-level variables of type `Term`, they are instead encoded as elements of an abstract type `V`, and there is an explicit constructor `var` for variables:

```
module PHOAS where
  data Term (V : Set) : Set where
    var : V → Term V
    lam : (V → Term V) → Term V
    app : Term V → Term V → Term V

  ex : ∀ {V} → Term V
  ex = lam (λ f → lam (λ x → app (var f) (var x)))

```

This type does not suffer from issues with positivity, it is possible to check whether a term is a variable, and exotic terms are ruled out since there is no way to pattern match on an element of the abstract type parameter `V`. Yet it preserves the good property that terms are well-scoped by construction and that α-equivalent terms are equal.

Still, just from the fact that it is a higher-order representation, PHOAS can be challenging to use in practice. In particular, defining simple operations involves coming up with clever ways to instantiate the parameter `V`; for example pretty-printing a term can be done by instantiating `V` to be `String`:

```
  pp : ℕ → Term String → String
  pp fresh (var x)    = x
  pp fresh (lam f)    =
    let name = "x" ++ ℕ.show fresh
    in  "λ " ++ name ++ ". " ++ pp (suc fresh) (f name)
  pp fresh (app u v)  = case u of λ where
    (var x) → x ++ " " ++ pp fresh v
    _       → "(" ++ pp fresh u ++ ") " ++ pp fresh v

  _ : pp 0 ex ≡ "λ x0. λ x1. x0 x1"
  _ = refl

```

Other algorithms might require functional extensionality or parametricity results to reason correctly about the behaviour of the syntax. Altogether, it seems to me these reasons imply PHOAS is less well suited for implementing actual algorithms on syntax, as opposed to purely doing metatheory (for which it was originally introduced).

## Well-scoped de Bruijn indices

If all we want from PHOAS is the fact that terms are well-scoped by construction, there is actually a much easier way to obtain that guarantee with de Bruijn indices: we can simply index the type by the number `n` of variables that are in scope, and require that indices are elements of `Fin n`. This is known as _well-scoped de Bruijn syntax_.

```
module WellScopedDB where
  data Term (n : ℕ) : Set where
    var : Fin n → Term n
    lam : Term (1 + n) → Term n
    app : Term n → Term n → Term n

  ex : Term 0
  ex = lam {-f-} (
         lam {-x-} (
           app (var {-f-} (suc zero))
               (var {-x-} zero)
         )
       )

```

One could criticize this for relying on dependent types in the meta-language. However, we can obtain a variant of well-typed de Bruijn syntax that does not require the use of dependent types by indexing directly by the set of variables in scope:

```
module PoorMansWellScoped where
  data Term (V : Set) : Set where
    var : V → Term V
    lam : Term (Maybe V) → Term V
    app : Term V → Term V → Term V

  ex : Term ⊥
  ex = lam {-f-} (
         lam {-x-} (
           app (var {-f-} (just nothing))
               (var {-x-} nothing)
         )
       )

```

This provides the same guarantees as well-scoped de Bruijn syntax, but can be implemented in Haskell ’98. However, elements of nested `Maybe` types are a bit harder to manipulate than elements of type `Fin`, and may lead to worse performance if `Fin`s end up being represented as machine integers. Also, you should just use a proper language that supports dependent types instead.

A more serious criticism I have against this representation is that while this representation makes it harder to write wrong transformations on syntax that mess up the variables, it does not really do anything to make _good_ de Bruijn terms easier to produce or understand for humans. For example, a term of type `Term 2` with two variables `x` and `y` in scope does not indicate whether `x` is `var 0` and `y` is `var 1` or vice versa.

Still, well-scoped de Bruijn syntax is used quite often in practice, for example in the [generic-syntax library](https://github.com/gallais/generic-syntax) for Agda. In fact, this library goes beyond the subject of this blog post in many ways, by providing a generic _universe_ of syntaxes with generic operations defined over them and by enforcing not just well-scopedness but also well-typedness. While these features are orthogonal to the topic of this blog post, I strongly encourage you to take a look at it.

## Well-scoped names

One criticism we had of de Bruijn syntax is the fact that it is very hard to understand by humans, and this problem is not really solved by switching to the well-scoped variant. We can solve this problem by - instead of indexing by just the number of variables in scope - indexing by the _scope itself_, represented as a list of names. Variables then contain two pieces of data: a name and a _proof_ that the name is in scope.

```
module WellScopedNames where
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)

  Scope = List String

  data Term (s : Scope) : Set where
    var : (x : String) → x ∈ s → Term s
    lam : (x : String) → Term (x ∷ s) → Term s
    app : Term s → Term s → Term s

  ex : Term []
  ex = lam "f" (
         lam "x" (
           app (var "f" (there (here refl)))
               (var "x" (here refl))
         )
       )

```

The result we get is a combination of named variables with well-scoped de Bruijn syntax. While the membership proofs are cumbersome to write by hand, it wouldn’t take much effort to implement a [macro](https://agda.readthedocs.io/en/v2.6.2/language/reflection.html#macros) that constructs them automatically.

While there is no fundamental difference in the guarantees offered by this representation and well-scoped de Bruijn syntax, having the names around is more intuitive for the programmer and can help to avoid errors when changing the order of variables in scope. However, having the names around also means we lose one advantage of de Bruijn syntax: two α-equivalent terms can now be distinguished by looking at the names of the variables.

One other thing one should keep in mind when using this representation is that it allows referring to shadowed names. For example, it is perfectly fine to name both variables `x` in the previous example:

```
  ex' : Term []
  ex' = lam "x" (
          lam "x" (
            app (var "x" (there (here refl)))
                (var "x" (here refl))
          )
        )

```

The reason for this is that the membership proof `x ∈ s` is _proof-relevant_: it consists of a path to the position where the variable is bound in the scope. While this can be considered as either a feature or a bug, it does mean one has to be careful with pretty-printing, since a naive approach would print the above term as `λ x. λ x. x x`, which is not correct. If desired, we could instead use a more sophisticated representations of scopes that enforces freshness as an _inductive-recursive type_:

```
module WellScopedFresh where

  data FreshList (A : Set) : Set
  _#_ : {A : Set} → A → FreshList A → Set

  data FreshList A where
    []    : FreshList A
    _∷_<_> : (x : A) (xs : FreshList A) → x # xs → FreshList A

  x # [] = ⊤
  x # (y ∷ xs < _ >) = x ≢ y × (x # xs)

  data _∈_ {A : Set} (x : A) : FreshList A → Set where
    here  : ∀ {xs p} → x ∈ (x ∷ xs < p >)
    there : ∀ {y xs p} → x ∈ xs → x ∈ (y ∷ xs < p >)

  Scope = FreshList String

  data Term (s : Scope) : Set where
    var : (x : String) → x ∈ s → Term s
    lam : (x : String) (p : x # s)
        → Term (x ∷ s < p >) → Term s
    app : Term s → Term s → Term s

  ex : Term []
  ex = lam "f" f# (
         lam "x" x#f (
           app (var "f" (there here))
               (var "x" here)
         )
       )
    where
      f# : "f" # []
      f# = tt

      x#f : "x" # ("f" ∷ [] < f# >)
      x#f = (λ ()) , tt

```

As you can see, this approach ensures that the names we bind are fresh w.r.t. the current scope, at the cost of more complex types and having to produce freshness proofs (although this could also be automated).

Despite its limitations I feel that the simple version using a normal list of names strikes a nice balance between getting good static guarantees and being easy to use. This is also attested by the fact it is used in the [bootstrapped implementation of Idris 2](https://github.com/idris-lang/Idris2/blob/21ca9066f13e3b9f8c6be28774a91f43bb68d51d/src/Core/TT.idr#L770-L778).

## Nameless, Painless

When I explained the nominal approach to name binding, I made use of an abstract interface exposing the operations. While this was done out of necessity (since Agda does not have nominal types built-in), working with an abstract interface for name binding actually has other benefits: it allows us to avoid relying on the implementation details of names by hiding them from the interface, and it even allows swapping out a concrete implementation of variables for another one (perhaps one that’s more efficient).

This is what the paper [“Nameless, Painless”](http://doi.acm.org/10.1145/2034773.2034817) does: it provides an abstract interface to well-scoped de Bruijn indices. The interface consists of an abstract type of `World`s (i.e. scopes), and for each world `w` a set of names `Name w`. In the concrete implementation of well-scoped de Bruijn syntax we gave above, these were implemented as `World = ℕ` and `Name = Fin` respectively.

```
module NamelessPainless where

  record NaPa : Set₁ where
    field
      World   : Set
      ∅       : World
      _↑1     : World → World
      Name    : World → Set
      _⊆_     : World → World → Set
      zeroᴺ   : ∀ {α} → Name (α ↑1)
      sucᴺ    : ∀ {α} → Name α → Name (α ↑1)
      _==ᴺ_   : ∀ {α} → Name α → Name α → Bool
      exportᴺ : ∀ {α} → Name (α ↑1) → Maybe (Name α)
      coerce  : ∀ {α β} → α ⊆ β → Name α → Name β
      ¬Name∅  : ¬ (Name ∅)


  open NaPa {{...}}

```

The operation `_==ᴺ_` allows us to compare two names in the same scope, and the function `exportᴺ` allows us to do case analysis on whether a name is bound by the top-level binder or one beneath it.

To actually define a syntax that uses this interface, we parametrize our module with an instance argument of type `NaPa`:

```
  module _ {{_ : NaPa}} where

    data Term (w : World) : Set where
      var : Name w → Term w
      lam : Term (w ↑1) → Term w
      app : Term w → Term w → Term w

    ex : ∀ {w} → Term w
    ex = lam {-f-} (
           lam {-x-} (
             app (var {-f-} (sucᴺ zeroᴺ))
                 (var {-x-} zeroᴺ)
            )
          )

```

Apart from the benefits mentioned above, we also get additional [free theorems](https://dl.acm.org/doi/pdf/10.1145/99370.99404) as a result of being parametric over the implementation of scopes and names. For example, the paper shows that any world-polymorphic function commutes with renaming of the free variables.

Despite these apparent strengths, I have not seen this approach being used in practice. I’m not sure that’s because it has some important downsides, or just because it is not well known.

## Abstract scope graphs

[_Scope graphs_](https://doi.org/10.1145/3276484) provide a very general interface for representing syntax with name binding and name resolution. Broadly speaking, nodes in a scope graph represent scopes, and edges determine reachability. Rather than formalize the full theory of scope graphs here, we can take the same approach as before and declare an abstract interface containing the pieces we need here (I apologize to my colleagues in Delft if I am horribly misrepresenting scope graphs):

```
module AbstractScopeGraphs where

  Name = String -- just for concreteness

  record ScopeGraph : Set₁ where
    field
      -- Structure of scope graphs we rely on:
      -- 1. a type of scopes (i.e. nodes in the graph)
      Scope : Set
      -- 2. a predicate expressing reachability + visibility
      _∈_   : Name → Scope → Set
      -- 3. Binding a name, shadowing all previous occurrences
      bind  : Name → Scope → Scope
      here  : ∀ {x s} → x ∈ bind x s
      there : ∀ {x y s} → x ≢ y → x ∈ s → x ∈ bind y s

  open ScopeGraph {{...}}

```

The definition of a scope graph relies on two core notions of _reachability_ and _visibility_ of a name in a scope. For simplicity both of them are combined into a single predicate `_∈_` in this interface. We can then define our syntax using `_∈_` and `bind`:

```
  module _ {{_ : ScopeGraph}} where

    data Term (s : Scope) : Set where
      var : (x : Name) → x ∈ s → Term s
      lam : (x : Name) → Term (bind x s) → Term s
      app : Term s → Term s → Term s

    ex : ∀ {s} → Term s
    ex {s} = lam "f" (
               lam "x" (
                 app (var "f" (there (λ ()) here))
                     (var "x" here)
               )
             )

```

The result is very similar to the approach using `FreshList` we defined above, except that now we use an abstract interface as in the Nameless, Painless approach. This means it is easier to extend the interface with more fine-grained notions (e.g. the distinction between reachability and visibility) that scope graphs allow us to model. It also allows us to scale up more easily to more complex name binding structures.

There’s still an issue that this approach shares with the `FreshList` approach: since the syntax of a lambda expression contains an element of type `Name`, it is possible to distinguish two α-equivalent names. Another possible drawback is that much of the generality of scope graphs is not actually needed, which might result in unneeded complexity (though the use of an abstract interface means this does not matter too much).

## The ‘Namely, Painless’ approach

In his [PhD thesis](https://nicolaspouillard.fr/publis/namely-painless-defense-version.pdf), Nicolas Pouillard (the main author of the “Nameless, Painless” paper) presents another interface for programming with names and binders called `NomPa` (for “Nominal, Painless”, I presume). In contrast to `NaPa`, it models syntax with named variables. Yet it avoids the problem discussed above, so _α-equivalent terms are indistinguishable_. The trick here is to have separate types for names and binders, and only expose equality checking of names in the interface:

```
module NamelyPainless where

  record NomPa : Set₁ where

    field
      World  : Set
      Name   : World → Set
      Binder : Set
      _◃_    : Binder → World → World

      zeroᴮ  : Binder
      sucᴮ   : Binder → Binder

      nameᴮ   : ∀ {α} b → Name (b ◃ α)
      binderᴺ : ∀ {α} → Name α → Binder

      ∅      : World
      ¬Name∅ : ¬ (Name ∅)

      _==ᴺ_   : ∀ {α} (x y : Name α) → Bool
      exportᴺ : ∀ {α b} → Name (b ◃ α)
              → Name (b ◃ ∅) ⊎ Name α

      _#_  : Binder → World → Set
      _#∅  : ∀ b → b # ∅
      suc# : ∀ {α b} → b # α → (sucᴮ b) # (b ◃ α)

      _⊆_     : World → World → Set
      coerceᴺ : ∀ {α b} → α ⊆ b → Name α → Name b
      ⊆-refl  : Reflexive _⊆_
      ⊆-trans : Transitive _⊆_
      ⊆-∅     : ∀ {α} → ∅ ⊆ α
      ⊆-◃     : ∀ {α β} b → α ⊆ β → (b ◃ α) ⊆ (b ◃ β)
      ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◃ α)

  open NomPa {{...}}

```

Note that names are bound to a specific world, so there is no way to compare names from different worlds.

```
  module Syntax {{_ : NomPa}} where

    data Term (w : World) : Set where
      var : Name w → Term w
      lam : (b : Binder) → Term (b ◃ w) → Term w
      app : Term w → Term w → Term w

    ex : Term ∅
    ex = lam fb (lam xb (app (var f) (var x)))
      where
        fb xb : Binder
        fb = zeroᴮ
        xb = sucᴮ zeroᴮ

        x-fresh : xb # (fb ◃ ∅)
        x-fresh = suc# (fb #∅)

        f = coerceᴺ (⊆-# x-fresh) (nameᴮ fb)
        x = nameᴮ xb

```

Just as with `NaPa`, we get nice free theorems by being parametric in the implementation of `NomPa`. For example, the parametricity theorem for `_==ᴺ_` tells us that checking equality commutes with renaming, hence α-equivalent terms are indeed treated equally.

As promised earlier, `NomPa` can be used to implement the interface we previously used for nominal signatures:

```
  module NominalNomPa {{_ : NomPa}} where
    Sort : Set₁
    Sort = World → Set

    Atom : Sort
    Atom = Name

    1ᵉ : Sort
    1ᵉ _ = ⊤

    _×ᵉ_ : Sort → Sort → Sort
    (E₁ ×ᵉ E₂) a = E₁ a × E₂ a

    _→ᵉ_ : Sort → Sort → Set
    (E₁ →ᵉ E₂) = ∀ {a} → E₁ a → E₂ a

    Pred   : Sort → Set₁
    Pred E = ∀ {a} → E a → Set

    absᵉ : Sort → Sort
    (absᵉ E) a = Σ[ b ∈ Binder ] (E (b ◃ a))

    data Term : Sort where
      var : Atom →ᵉ Term
      app : (Term ×ᵉ Term) →ᵉ Term
      lam : (absᵉ Term) →ᵉ Term

```

To check that this indeed results in a valid implementation of the nominal interfaces we wrote down before, we can instantiate the interfaces elegantly using the little-known [syntax for building record values from modules](https://agda.readthedocs.io/en/v2.6.2/language/record-types.html#building-records-from-modules).

```
  instance
    nominal : {{_ : NomPa}} → Nominal.Nominal
    nominal = record { NominalNomPa }

    nominalSyntax : {{_ : NomPa}} → Nominal.Syntax
    nominalSyntax = record { NominalNomPa }

```

`NomPa` has all the desirable properties of the various approaches mentioned before, and can in fact be used to model these approaches. So, is it the ultimate approach to modelling name binding in Agda? Well, who knows, as once again I have not found anywhere it is actually used, despite it being published in 2012. My main worry is that the interface is quite large, and hence could be complicated to use in practice.

## Co-de Bruijn indices

Since the invention of `NomPa`, there has been at least one more exciting development in the area of syntax with binders. In his [2018 paper “Everybody’s Got To Be Somewhere”](https://arxiv.org/abs/1807.04085v1), Conor McBride describes _co-deBruijn syntax_, a nameless representation where binding information is encoded completely in the structure of the terms rather than at the variables themselves. In particular, each term constructor remembers which variables are actually used by which subterm, removing the rest from the scope. When we arrive at a variable, all the unused variables have been removed from the scope, so there is but a single variable to pick.

Brutally stripping all the categorical concepts from the paper, one might end up with the following simplified type of scope coverings:

```
module CoDeBruijn where

  variable
    k l m n : ℕ

  data Cover : (k l m : ℕ) → Set where
    done   :               Cover      0       0       0
    left   : Cover k l m → Cover (suc k)      l  (suc m)
    right  : Cover k l m → Cover      k  (suc l) (suc m)
    both   : Cover k l m → Cover (suc k) (suc l) (suc m)

```

An element of type `Cover k l m` says for each of `m` variables whether they are used just in the `left` subterm, just in the `right` subterm, or in `both` subterms. The left and right subterms thus should have `k` and `l` variables in scope respectively. Crucially there is no case for `neither`, hence the slogan “everybody’s got to be somewhere”.

We can then define our well-scoped co-deBruijn syntax using `Cover`:

```
  data Term : ℕ → Set where
    var  : Term 1
    lam  : Term (suc n) → Term n
    lam' : Term n → Term n  -- argument is not used
    app  : Cover k l m → Term k → Term l → Term m

  ex : Term 0
  ex = lam {-f-} (
         lam {-x-} (
           app (right (left done))
               (var {-f-}) (var {-x-})
         )
       )

```

There are two constructors for lambda abstraction: one for functions that use their argument and one for functions that don’t (I’m sure there’s a more elegant way to do this, but this works).

The great advantage of using co-deBruijn syntax is that scopes are always maximally precise: there is never any need to strengthen a term to get rid of an unused variable. On the flip side, co-deBruijn syntax is even more unintuitive and difficult to understand for humans than regular de Bruijn syntax. Quoting the author: _“Co-de-Bruijn representation is even less suited to human comprehension than de Bruijn syntax, but its informative precision makes it all the more useful for machines. Dependency checking is direct, so syntactic forms like vacuous functions or η-redexes are easy to spot.”_

To make the syntax more comprehensible to mere mortals, we can do the same we did for de Bruijn syntax and represent scopes as lists of names:

```
module NamedCoDeBruijn where

  Name  = String
  Scope = List Name

  variable
    x y z    : Name
    xs ys zs : Scope

  data Cover : (xs ys zs : Scope) → Set where
    done   :                  Cover      []       []       []
    left   : Cover xs ys zs → Cover (z ∷ xs)      ys  (z ∷ zs)
    right  : Cover xs ys zs → Cover      xs  (z ∷ ys) (z ∷ zs)
    both   : Cover xs ys zs → Cover (z ∷ xs) (z ∷ ys) (z ∷ zs)

```

Doing this leads to a syntax that is much more pleasant to use (at least if we pick unique names):

```
  data Term : Scope → Set where
    var  : (x : Name) → Term (x ∷ [])
    lam  : (x : Name) → Term (x ∷ xs) → Term xs
    lam' : (x : Name) → Term xs → Term xs
    app  : Cover xs ys zs → Term xs → Term ys → Term zs

  ex : Term []
  ex = lam "f" (
         lam "x" (
           app (right (left done))
               (var "f") (var "x")
         )
       )

```

The remaining ugliness is the `Cover` proof needed at each application, however as before writing a macro that constructs these automatically should not be difficult.

One could imagine generalizing this further and defining an abstract interface like `NomPa` for working with co-deBruijn syntax. However, this post is plenty long as it is, so I’ll leave that as an exercise to the reader.

## Overview and conclusion

The goal of this blog post was mainly to give an overview of the various different approaches one could use when defining syntax with binders in Agda. Below is a table summarizing with the approaches I described, plus the benefits they provide to the programmer:

-   **First-order representation**: does the representation avoid the use of meta-level functions as part of the data structure? If not, it can be difficult or impossible to do things like checking equality of terms or pretty-printing.
    
-   **Named variables**: When I write down a piece of syntax, are variables represented by their names or anonymously? This provides some measure of readability by humans.
    
-   **Enforces α-equivalence**: Does the representation enforce that two α-equivalent terms are treated in the same way?
    
-   **Enforces well-scopedness**: Does the representation enforce that names can only be used when they are in fact in scope?
    
-   **No mixing of scopes**: Does the representation enforce that a name that comes from one scope is not used in a different scope?
    
-   **Abstract interface**: Does the representation provide an abstract interface that can be instantiated in different ways?
    
-   **Enforces freshness**: Does the representation allow us to require that names must be fresh at certain positions in the syntax?
    
-   **Strengthening is no-op**: Can we remove unused names from the scope without having to change the syntax?
    

So here’s the full table:

|  | Bare | DeBr | LoNa | Nom | PHOAS | WTDB | WTDB+N | FreshL | NaPa | ASG | NomPa | CoDB | CoDB+N |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| First-order representation | X | X | X | X |  | X | X | X | X | X | X | X | X |
| Named variables | X |  | X | X | X |  | X | X |  | X | X |  | X |
| Enforces α-equivalence |  | X | X |  | X | X |  |  | X |  | X | X |  |
| Enforces well-scopedness |  |  |  |  | X | X | X | X | X | X | X | X | X |
| No mixing of scopes |  |  |  |  |  |  | X | X |  | X | X |  | X |
| Enforces freshness |  |  |  | X |  |  |  | X |  | X | X |  |  |
| Abstract interface |  |  |  | X |  |  |  |  | X | X | X |  |  |
| Strengthening is no-op | X |  |  |  |  |  |  |  |  |  |  | X | X |

As a next step, it would be interesting to perform a comparison of (some of) these approaches on a practical application. My idea would be to define variants of the [reflection syntax of Agda](https://agda.readthedocs.io/en/latest/language/reflection.html#terms) using a few different approaches (it currently uses de Bruijn syntax), and test which one makes macros easier to write. This would also allow a proper performance evaluation to see the effect of the variable representation on the performance of syntax transformations. And of course my (not so) secret goal is to eventually use one of these representations for the definition of [Agda Core](https://jesper.sikanda.be/posts/veni-announcement.html)!

I’m very curious to hear your thoughts about this overview, whether I have missed any important criteria in this comparison, whether I have seriously misrepresented some of the approaches, whether I skipped one completely. In any of these cases, please let me know via [Zulip](https://agda.zulipchat.com/), [Twitter](https://twitter.com/agdakx), or [mail](mailto:jesper@sikanda.be).