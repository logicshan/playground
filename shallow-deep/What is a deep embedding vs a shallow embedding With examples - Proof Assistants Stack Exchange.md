The terms "deep" and "shallow" embedding are somewhat informal and have many variations. I will explain the essentials only.

An embedding from a source language $S$ to a target language $T$ is **shallow** if the constituent parts of $S$ are translated (mostly) directly to the corresponding parts of $T$. This is useful when we want to _use_ $S$ but all we have is $T$. For example, if $S$ is a domain-specific logic and $T$ is a full-fledged proof assistant, we encode $S$ using the logic of $T$ and then use $T$'s theorem proving abilities to prove $S$\-theorems. Even more specifically, suppose $S$ is the classical propositional calculus and $T$ is a proof assistant based on constructive type theory, equipped with a tactic for proving intuitionistic propositions. We can shallowly translate $S$ into $T$ using the [double-negation translation](https://en.wikipedia.org/wiki/Double-negation_translation) and use $T$'s tactic to prove classical $S$\-statements.

An embedding is **deep** if in $T$ we define (inductive) types that describe the syntax and inference rules of $S$. This is useful when we want to use $T$ to study $S$ as a formal system. For example, if $S$ is a programming language and $T$ is a full-fledged proof assistant, we can define in $T$ types that represent the syntax, the typing rules, and the operational semantics of $S$. This allows us to prove theorems _about_ $S$, such as [type safety](https://en.wikipedia.org/wiki/Type_safety). (In fact, this was one of successful early applications of proof assistant technology.)

### Example: simply-typed $\lambda$\-calculus

Suppose $S$ is the simply typed $\lambda$\-calculus with the following parts:

-   the types of natural numbers `nat`
-   function types, written `a ⇒ b`
-   constructors `zero` and `succ`
-   $\lambda$\-abstraction $\lambda (x{:}A),\, e$ and application $e_1 \, e_2$.

There are also typing contexts and typing rules which I am not going to write here, as they are quite standard (and also formalized below as a deep embedding in Agda).

#### Shallow embedding

The following is a shallow embedding of the calculus in Agda. It is mostly just a collection of abbreviations, so that we can write `nat` instead of Agda's `ℕ`, and `A ⇒ B` instead of Agda's `A → B`, etc.

(Note: the embedding shown below is not as shallow as it could be, because we map the typing contexts of λ-calulus to types in Agda. An even shallower embedding would map contexts to contexts, but that would be a bit confusing to beginners because most of the embedding would become invisible.)

```
module Shallow where

  open import Data.Nat
  open import Data.Product
  open import Data.Unit

  -- The types of the λ-calculus are Agda's types.
  type = Set

  -- The typing contexts are sets.
  context = Set

  -- The empty context is the unit type
  ∙ : context
  ∙ = ⊤

  -- Extending a context with type is Agda's cartesian product
  infixl 5 _⨟_
  _⨟_ : context → type → context
  Γ ⨟ A = Γ × A

  -- The λ-calculus type nat is Agda's type ℕ
  nat : type
  nat = ℕ

  -- The λ-calculus function type is Agda's function type
  infixr 7 _⇒_
  _⇒_ : type → type → type
  A ⇒ B = A → B

  -- The λ-calculus typing judgement x : nat, f : nat ⇒ nat, y : nat ⊢ succ (succ x) : nat
  example-1 : (∙ ⨟ nat ⨟ nat ⇒ nat ⨟ nat) → nat
  example-1 (((_ , x) , f) , y) = suc (suc x)

  -- The λ-calculus typing judgement ∙ ⊢ (λ (x y : nat) succ x) (succ (succ 0))
  example-2 : ∙ → nat ⇒ nat
  example-2 tt = (λ (x y : nat) → suc x) (suc (suc 0))

  -- The λ-calculus typing judgement f : A ⇒ A ⊢ λ (x : A) f (f x) : A ⇒ A
  example-3 : {A : type} → (∙ ⨟ A ⇒ A) → (A ⇒ A)
  example-3 {A} (_ , f) = λ (x : A) → f (f x)
```

With the shallow embedding it is very easy to compute in λ-calculus, just use Agda's normalization abilities to compute their normal forms. This is possible because our embedding makes sure that the λ-calculus normalization and Agda's normalization coincide.

### Deep embedding

Here is the corresponding deep embedding.

```

module Deep where

  -- The λ-calculus simple types
  infixr 7 _⇒_
  data type : Set where
    nat : type
    _⇒_ : type → type → type

  -- The λ-calculus typing context, we use de Bruijn indices
  infixl 5 _⨟_
  data context : Set where
    ∙ : context
    _⨟_ : context → type → context

  -- A ∈ Γ is the type of those de Bruijn indices whose type in Γ is A
  infix 3 _∈_
  data _∈_ : type → context → Set where
    z : ∀ {A : type} {Γ : context} → A ∈ Γ ⨟ A
    s : ∀ {A B : type} {Γ : context} → B ∈ Γ → B ∈ Γ ⨟ A

  -- term Γ A is the type of λ-calculus terms of type A in context Γ
  data term : context → type → Set where
    zero : ∀ {Γ} → term Γ nat
    succ : ∀ {Γ} → term Γ nat → term Γ nat
    var : ∀ {Γ A} → A ∈ Γ → term Γ A
    lam : ∀ {Γ} A {B} → term (Γ ⨟ A) B → term Γ (A ⇒ B)
    app : ∀ {Γ A B} → term Γ (A ⇒ B) → term Γ A → term Γ B

  -- The λ-calculus typing judgement x : nat ⨟ f : nat ⇒ nat⨟ y : nat ⊢ succ (succ x) : nat
  example-1 : term (∙ ⨟ nat ⨟ nat ⇒ nat ⨟ nat) nat
  example-1 = succ (succ (var (s (s z))))

  -- The λ-calculus typing judgement ∙ ⊢ (λ (x y : nat) succ x) (succ (succ 0)) : nat ⇒ nat
  example-2 : term ∙ (nat ⇒ nat)
  example-2 = app (lam nat (lam nat (succ (var (s z))))) (succ (succ zero) )

  -- The λ-calculus typing judgement f : A ⇒ A ⊢ λ (x : A) f (f x) : A ⇒ A
  example-3 : {A : type} → term (∙ ⨟ A ⇒ A) (A ⇒ A)
  example-3 {A} = lam A (app (var (s z)) (app (var (s z)) (var z)))
```

In the deep embedding the terms of the λ-calculus are elements of the inductive type `term`. We cannot use Agda's normalization algorithm to compute with these, they're all in normal form already.

However, with the deep embedding we can reason _about_ λ-calculus. For example, we can define a model of the λ-calculus:

```
module Semantics where

  -- The set-theoretic model of λ-calculus

  open import Data.Nat
  open import Data.Unit
  open import Data.Product

  open Deep

  -- Types are interpreted as sets
  ⟦_⟧ᵗ : type → Set
  ⟦ nat ⟧ᵗ = ℕ
  ⟦ A ⇒ B ⟧ᵗ = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

  -- Contexts are interpreted as sets
  ⟦_⟧ᶜ : context → Set
  ⟦ ∙ ⟧ᶜ = ⊤
  ⟦ Γ ⨟ A ⟧ᶜ =  ⟦ Γ ⟧ᶜ × ⟦ A ⟧ᵗ

  -- Auxiliary map, for looking up values of variables
  lookup : ∀ {Γ A} → A ∈ Γ → ⟦ Γ ⟧ᶜ → ⟦ A ⟧ᵗ
  lookup z (_ , a) = a
  lookup (s x) (η , _) = lookup x η

  -- A typing judgement Γ ⊢ e : A is interpreted as a map ⟦ e ⟧ : ⟦ Γ ⟧ᶜ → ⟦ A ⟧ᵗ
  ⟦_⟧ : ∀ {Γ A} → term Γ A → ⟦ Γ ⟧ᶜ → ⟦ A ⟧ᵗ
  ⟦ zero ⟧ η = 0
  ⟦ succ e ⟧ η = suc (⟦ e ⟧ η)
  ⟦ var x ⟧ η = lookup x η
  ⟦ lam A e ⟧ η = λ a → ⟦ e ⟧ (η , a)
  ⟦ app e₁ e₂ ⟧ η = ⟦ e₁ ⟧ η (⟦ e₂ ⟧ η)

  -- The interpretation of ∙ ⊢ (λ (x : nat) . succ (succ x)) (succ zero) : nat
  cow : ⟦ ∙ ⟧ᶜ → ⟦ nat ⟧ᵗ
  cow tt = ⟦ app (lam nat (succ (succ (var z)))) (succ zero) ⟧ tt
  -- Agda normalizes cow tt to the numeral 3
```

Yes, the model is also an interpreter for λ-calculus. Welcome to constructive mathematics.

### The laundry list

I am not familiar with all the embeddings you listed in the question. Hopefully other will provide answers for the missing ones:

-   “Coq in Coq” is deep. They want to prove things _about_ Coq. A shallow embedding would be the identity map.
-   Dedukti is a [logical framework](https://en.wikipedia.org/wiki/Logical_framework), which makes it a bit special. Its purpose is formalization of formal systems. One defines the syntax and typing rules of the embedded system (deep embedding), but in such a way that Dedukti's contexts, variables, type-checking, normalization and rewriting abilities can be reused by the embedded system (shallow embedding).
-   “Coq is a Lean Typechecker“ is shallow. The web page even says: “The basic idea is to translate Lean Prop to Coq SProp, inductives to inductives, etc.“
-   “Towards self-verification of HOL Light” has a section called “Formalized syntax” so I will guess it is deep without reading the entire paper.
-   “Lean4Lean“ is about implementing Lean in Lean, a [self-interpreter](https://en.wikipedia.org/wiki/Interpreter_(computing)#Self-interpreter). This is a deep embedding because it will involve parsing syntax and interpreting it into machine code. A shallow embedding of Lean in Lean is just the identity transformation.
-   “MathPort” is a shallow embedding, because they tried as hard as possible to make it the identity transformation.
-   “Encoding the HOL Light logic in Coq” is shallow.

#### Supplemental: What about set theories?

An interesting question is whether emeddings of set theory into type theory are shallow or deep. Let us just focus on [material set theory](https://ncatlab.org/nlab/show/material+set+theory) such as ZFC (although the story is much the same for [structural set thoeries](https://ncatlab.org/nlab/show/structural+set+theory)).

A material set theory is typically a single-sorted first-order theory. In type theory we commonly find something like this:

```
open import Level
open import Data.Empty
open import Data.Product
open Σ

module SetTheory (ℓ : Level) where

  -- The type of well-founded trees with branching type from universe level ℓ
  data V : Set (suc ℓ) where
    set : ∀ {I : Set ℓ} → (I → V) → V

  mutual
    -- Membership relation
    infix 5 _∈_
    data _∈_ : V → V → Set ℓ where
      ∈-set : ∀ {I} {t} {u : I → V} → (Σ[ i ∈ I ] t ≈ u i) → t ∈ set u

    -- Subset relation
    infix 5 _⊆_
    _⊆_ : V → V → Set ℓ
    set x ⊆ t = ∀ i → x i ∈ t

    -- Equality of well-founded trees as sets
    infix 5 _≈_
    data _≈_ : V → V → Set ℓ where
      ≈-set : ∀ {t u : V} → t ⊆ u → u ⊆ t  → u ≈ t

  -- We check that (V, ∈, ≈) satisfies the set-theoretic axioms.
  -- For illustration we only provide extensionality and empty set.
  -- (Note that we cannot validate the powerset axiom, Agda is too predicative.)

  data empty-type : Set ℓ where

  ∅ : V
  ∅ = set {I = empty-type} λ {()}

  axiom-empty-set : Σ[ x ∈ V ] ∀ (y : V) → y ∈ x → ⊥
  axiom-empty-set = ∅ , λ {y (∈-set ())}

  axiom-extensionality : ∀ {x y : V} → x ⊆ y → y ⊆ x → x ≈ y
  axiom-extensionality x⊆y y⊆x = ≈-set y⊆x x⊆y

  -- and so on
```

I would call this a _model_ of set theory in type theory. It is not an "embedding" in the sense of having a syntactic translation from one formal system to another.

This situation is completely analogous to other situations involving first-order theories, which is what a material set theory usually is. Take the theory of a group, for example. If we define a _single_ group, say $\mathbb{Z}_7$, then that is like defining a single model `V` of set theory, as above. We might define the structure of _all groups_

```
structure Group : Type where
  carrier : Type
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  assoc : ...
  unit-left : ...
  unit-right : ...
  inv-left : ...
  inv-right : ...
```

but that would still just be _semantics_, as we're now just defining (the object part of) the category of all groups. We could to the same for set theories and define the category of all models of set theory, so not an embedding.

If you insist, you may call the above a _shallow_ something-or-other of set theory into type theory (because we are using type-theoretic logic to validate set-theoretic axioms), but I hesitate to call it an "embedding" because it does not faithfully reflect provability of set-theoretic statements. That is, type theory might prove some set-theoretic statements about `V` which set theory does not prove (this is not an easily answered question, and it depends on the exact set-theoretic axioms and the exact type-theoretic rules).

A deep embedding of set theory into type theory would begin with inductive types representing the first-order formulas and terms. But that's a different kind of animal that we would use if we wanted to prove meta-theorems _about_ the first-order theory known as "set theory".