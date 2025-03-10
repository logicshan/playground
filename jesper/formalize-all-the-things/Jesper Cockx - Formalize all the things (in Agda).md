Posted by Jesper on October 4, 2019

I quite often hear from people that they are interested in learning Agda, and that’s great! However, I often feel there are not enough examples out there of how to use the different features of Agda to implement programs, enforce invariants in their types, and prove their properties. So in this blog post I hope to address exactly that problem.

![](https://jesper.sikanda.be/images/formalize-all-the-stuff.jpg)

The main goal of this example is to show off the dual purpose of Agda as a strongly typed programming language and as a proof assistant for formalizing mathematics. Since both purposes are part of the same language, each of them reinforces the other: we can prove properties of our programs, and we can write programs that produce proofs. In this example, we will see this power in action by (1) defining the mathematical structure of partial orders, (2) implementing a generic binary search trees and insertion of new elements into them, and (3) proving that this function is implemented correctly.

This blog post was based on a talk I gave at the [Initial Types Club](https://github.com/InitialTypes/Club) at Chalmers.

## Preliminaries

For this post we keep the dependencies to a minimum so we don’t rely on the standard library. Instead, we import some of the built-in modules of Agda directly.

```
open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

```

A [`variable` declaration](https://agda.readthedocs.io/en/v2.6.0.1/language/generalization-of-declared-variables.html) (since Agda 2.6.0) allows us to use variables without binding them explicitly. This means they are implicitly universally quantified in the types where they occur.

```
variable
  A B C : Set
  x y z : A
  k l m n : Nat

```

In the code that follows, we will use [instance arguments](https://agda.readthedocs.io/en/v2.6.0.1/language/instance-arguments.html) to automatically construct some proofs. When working with instance arguments, the `it` function below is often very useful. All it does is ask Agda to please fill in the current argument by using a definition that is marked as an `instance`. (More about instance arguments later).

```
it : {{x : A}} → A
it {{x}} = x

```

(Unary) natural numbers are defined as the datatype `Nat` with two constructors `zero : Nat` and `suc : Nat → Nat`. We use the ones imported from `Agda.Builtin.Nat` because they allow us to write literal numerals as well as constructor forms.

```
_ : Nat
_ = zero + 7 * (suc 3 - 1)

```

(Definitions that are named `_` are typechecked by Agda but cannot be used later on. This is often used to define examples or test cases).

We can define [parametrized datatypes](https://agda.readthedocs.io/en/v2.6.0.1/language/data-types.html#parametrized-datatypes) and functions by [pattern matching](https://agda.readthedocs.io/en/v2.6.0.1/language/function-definitions.html) on them. For example, here is the equivalent of Haskell’s `Maybe` type.

```
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing :     Maybe A

mapMaybe : (A → B) → (Maybe A → Maybe B)
mapMaybe f (just x) = just (f x)
mapMaybe f nothing = nothing

```

Note how `A` and `B` are implicitly quantified in the type of `mapMaybe`!

## Quick recap on the Curry-Howard correspondence

The Curry-Howard correspondence is the core idea that allows us to use Agda as both a programming language and a proof assistant. Under the Curry-Howard correspondence, we can interpret logical propositions (A ∧ B, ¬A, A ⇒ B, …) as the types of all their possible proofs.

A proof of ‘A and B’ is a _pair_ (x , y) of a proof `x : A` and an proof `y : B`.

```
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

```

A proof of ‘A or B’ is either `inl x` for a proof `x : A` or `inr y` for a proof `y : B`.

```
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

mapInl : (A → B) → A ⊎ C → B ⊎ C
mapInl f (inl x) = inl (f x)
mapInl f (inr y) = inr y

mapInr : (B → C) → A ⊎ B → A ⊎ C
mapInr f (inl x) = inl x
mapInr f (inr y) = inr (f y)

```

A proof of ‘A implies B’ is a transformation from proofs `x : A` to proofs of `B`, i.e. a function of type `A → B`.

‘true’ has exactly one proof `tt : ⊤`. We could define this as a datatype with a single constructor `tt`, but here we define it as a record type instead. This has the advantage that Agda will use eta-equality for elements of `⊤`, i.e. `x = y` for any two variables `x` and `y` of type `⊤`.

```
record ⊤ : Set where
  constructor tt     -- no fields

```

‘false’ has no proofs.

```
data ⊥ : Set where   -- no constructor

```

‘not A’ can be defined as ‘A implies false’.

```
¬_ : Set → Set
¬ A = A → ⊥

```

### Examples

```
-- “If A then B implies A”
ex₁ : A → (B → A)
ex₁ = λ z _ → z

-- “If A and true then A or false”
ex₂ : (A × ⊤) → (A ⊎ ⊥)
ex₂ = λ z → inl (fst z)

-- “If A implies B and B implies C then A implies C”
ex₃ : (A → B) → (B → C) → (A → C)
ex₃ = λ f g z → g (f z)

-- “It is not the case that not (either A or not A)”
ex₄ : ¬ (¬ (A ⊎ (¬ A)))
ex₄ = λ f → f (inr (λ x → f (inl x)))

```

Since Agda’s logic is constructive, it is not possible to prove the direct version of `ex₄` (`A ⊎ (¬ A)`).

## Equality

To state many properties of our programs, we need the notion of equality. In Agda, equality is defined as the datatype `_≡_` with one constructor `refl : x ≡ x` (imported from `Agda.Builtin.Equality`).

```
_ : x ≡ x
_ = refl

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

```

## Ordering natural numbers

The standard ordering on natural numbers can be defined as an [_indexed datatype_](https://agda.readthedocs.io/en/v2.6.0.1/language/data-types.html#indexed-datatypes) with two indices of type `Nat`:

```
module Nat-≤ where

  data _≤_ : Nat → Nat → Set where
    ≤-zero :         zero  ≤ n
    ≤-suc  : m ≤ n → suc m ≤ suc n

  ≤-refl : n ≤ n
  ≤-refl {n = zero}  = ≤-zero
  ≤-refl {n = suc k} = ≤-suc ≤-refl

  ≤-trans : k ≤ l → l ≤ m → k ≤ m
  ≤-trans ≤-zero      l≤m         = ≤-zero
  ≤-trans (≤-suc k≤l) (≤-suc l≤m) =
    ≤-suc (≤-trans k≤l l≤m)

  ≤-antisym : m ≤ n → n ≤ m → m ≡ n
  ≤-antisym ≤-zero      ≤-zero      = refl
  ≤-antisym (≤-suc m≤n) (≤-suc n≤m) =
    cong suc (≤-antisym m≤n n≤m)

```

Now we can prove statements like `3 ≤ 5` as follows:

```
  _ : 3 ≤ 5
  _ = ≤-suc (≤-suc (≤-suc ≤-zero))

```

However, to prove an inequality like `9000 ≤ 9001` we would have to write 9000 `≤-suc` constructors, which would get very tedious. Instead, we can use Agda’s [instance arguments](https://agda.readthedocs.io/en/v2.6.0.1/language/instance-arguments.html) to automatically construct these kind of proofs.

To do this, we define an ‘instance’ that automatically constructs a proof of `m ≤ n` when m and n are natural number literals. A definition `inst : A` that is marked as an ‘instance’ will be used to automatically construct the implicit argument to functions with a type of the form `{{x : A}} → B`.

For efficiency reasons, we don’t mark the constructors `≤-zero` and `≤-suc` as instances directly. Instead, we make use of the efficient boolean comparison `_<_` (imported from `Agda.Builtin.Nat`) to construct the instance when the precondition `So (m < suc n)` is satisfied.

```
  So : Bool → Set
  So false = ⊥
  So true  = ⊤

  instance
    ≤-dec : {p : So (m < suc n)} → m ≤ n
    ≤-dec {m = zero} {n = n} = ≤-zero
    ≤-dec {m = suc m} {n = suc n} {p = p} =
      ≤-suc (≤-dec {p = p})

  _ : 9000 ≤ 9001
  _ = it

```

## Partial orders

We’d like to talk not just about orderings on concrete types like `Nat`, but also about the general concept of a ‘partial order’. For this purpose, we define a typeclass `Ord` that contains the type `_≤_` and proofs of its properties.

```
record Ord (A : Set) : Set₁ where
  field
    _≤_       : A → A → Set
    ≤-refl    : x ≤ x
    ≤-trans   : x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : x ≤ y → y ≤ x → x ≡ y

  _≥_ : A → A → Set
  x ≥ y = y ≤ x

```

Unlike in Haskell, typeclasses are not a primitive concept in Agda. Instead, we use the special syntax `open Ord {{...}}` to bring the fields of the record in scope as instance functions with a type of the form `{A : Set}{{r : Ord A}} → ...`. Instance search will then kick in to find the right implementation of the typeclass automatically.

```
open Ord {{...}}

```

We now define some concrete instances of the typeclass using [copattern matching](https://agda.readthedocs.io/en/v2.6.0.1/language/copatterns.html)

```
instance
  Ord-Nat : Ord Nat
  _≤_       {{Ord-Nat}} = Nat-≤._≤_
  ≤-refl    {{Ord-Nat}} = Nat-≤.≤-refl
  ≤-trans   {{Ord-Nat}} = Nat-≤.≤-trans
  ≤-antisym {{Ord-Nat}} = Nat-≤.≤-antisym

instance
  Ord-⊤ : Ord ⊤
  _≤_       {{Ord-⊤}} = λ _ _ → ⊤
  ≤-refl    {{Ord-⊤}} = tt
  ≤-trans   {{Ord-⊤}} = λ _ _ → tt
  ≤-antisym {{Ord-⊤}} = λ _ _ → refl

module Example (A : Set) {{A-≤ : Ord A}} where

  example : {x y z : A} → x ≤ y → y ≤ z → z ≤ x → x ≡ y
  example x≤y y≤z z≤x = ≤-antisym {A = A} x≤y (≤-trans {A = A} y≤z z≤x)

```

For working with binary search trees, we need to be able to decide for any two elements which is the bigger one, i.e. we need a _total_, _decidable_ order.

```
data Tri {{_ : Ord A}} : A → A → Set where
  less    : {{x≤y : x ≤ y}} → Tri x y
  equal   : {{x≡y : x ≡ y}} → Tri x y
  greater : {{x≥y : x ≥ y}} → Tri x y

record TDO (A : Set) : Set₁ where
  field
    {{Ord-A}} : Ord A               -- superclass Ord
    tri       : (x y : A) → Tri x y

open TDO {{...}} public

triNat : (x y : Nat) → Tri x y
triNat zero zero = equal
triNat zero (suc y) = less
triNat (suc x) zero = greater
triNat (suc x) (suc y) with triNat x y
... | less    {{x≤y}} = less    {{x≤y = Nat-≤.≤-suc x≤y}}
... | equal   {{x≡y}} = equal   {{x≡y = cong suc x≡y}}
... | greater {{x≥y}} = greater {{x≥y = Nat-≤.≤-suc x≥y}}

instance
  TDO-Nat : TDO Nat
  Ord-A {{TDO-Nat}} = Ord-Nat
  tri   {{TDO-Nat}} = triNat

```

## Binary search trees

In a dependently typed language, we can encode invariants of our data structures by using _indexed datatypes_. In this example, we will implement binary search trees by a lower and upper bound to the elements they contain (see [How to Keep Your Neighbours in Order](https://personal.cis.strath.ac.uk/conor.mcbride/Pivotal.pdf) by Conor McBride).

Since the lower bound may be -∞ and the upper bound may be +∞, we start by providing a generic way to extend a partially ordered set with those two elements.

```
data [_]∞ (A : Set) : Set where
  -∞  :     [ A ]∞
  [_] : A → [ A ]∞
  +∞  :     [ A ]∞

variable
  lower upper : [ A ]∞

module Ord-[]∞ {A : Set} {{ A-≤ : Ord A}} where

  data _≤∞_ : [ A ]∞ → [ A ]∞ → Set where
    -∞-≤ :          -∞   ≤∞   y
    []-≤ : x ≤ y → [ x ] ≤∞ [ y ]
    +∞-≤ :           x   ≤∞  +∞

  []∞-refl : x ≤∞ x
  []∞-refl { -∞}   = -∞-≤
  []∞-refl {[ x ]} = []-≤ (≤-refl {A = A})
  []∞-refl { +∞}   = +∞-≤

  []∞-trans : x ≤∞ y → y ≤∞ z → x ≤∞ z
  []∞-trans -∞-≤       _          = -∞-≤
  []∞-trans ([]-≤ x≤y) ([]-≤ y≤z) = []-≤ (≤-trans {A = A} x≤y y≤z)
  []∞-trans _          +∞-≤       = +∞-≤

  []∞-antisym : x ≤∞ y → y ≤∞ x → x ≡ y
  []∞-antisym -∞-≤       -∞-≤       = refl
  []∞-antisym ([]-≤ x≤y) ([]-≤ y≤x) = cong [_] (≤-antisym x≤y y≤x)
  []∞-antisym +∞-≤       +∞-≤       = refl

  instance
    Ord-[]∞ : {{_ : Ord A}} → Ord [ A ]∞
    _≤_       {{Ord-[]∞}} = _≤∞_
    ≤-refl    {{Ord-[]∞}} = []∞-refl
    ≤-trans   {{Ord-[]∞}} = []∞-trans
    ≤-antisym {{Ord-[]∞}} = []∞-antisym

open Ord-[]∞ public

```

We define some instances to automatically construct inequality proofs.

```
module _ {{_ : Ord A}} where

  instance
    -∞-≤-I : {y : [ A ]∞} → -∞ ≤ y
    -∞-≤-I = -∞-≤

    +∞-≤-I : {x : [ A ]∞} → x ≤ +∞
    +∞-≤-I = +∞-≤

    []-≤-I : {x y : A} {{x≤y : x ≤ y}} → [ x ] ≤ [ y ]
    []-≤-I {{x≤y = x≤y}} = []-≤ x≤y

```

Now we are (finally) ready to define binary search trees.

```
data BST (A : Set) {{_ : Ord A}}
         (lower upper : [ A ]∞)  : Set where

  leaf : {{l≤u : lower ≤ upper}}
       → BST A lower upper

  node : (x : A)
       → BST A lower [ x ]
       → BST A [ x ] upper
       → BST A lower upper

_ : BST Nat -∞ +∞
_ = node 42
      (node 6    leaf leaf)
      (node 9000 leaf leaf)

```

Note how instances help by automatically filling in the proofs that the bounds are satisfied! Somewhat more explicitly, the tree looks as follows:

```
_ : BST Nat -∞ +∞
_ = node 42
      (node 6    (leaf {{l≤u = -∞≤6}})    (leaf {{l≤u = 6≤42}}))
      (node 9000 (leaf {{l≤u = 42≤9000}}) (leaf {{l≤u = 9000≤+∞}}))

  where
    -∞≤6 : -∞ ≤ [ 6 ]
    -∞≤6 = it

    6≤42 : [ 6 ] ≤ [ 42 ]
    6≤42 = it

    42≤9000 : [ 42 ] ≤ [ 9000 ]
    42≤9000 = it

    9000≤+∞ : [ 9000 ] ≤ +∞
    9000≤+∞ = it

```

Next up: defining a lookup function. The result of this function is not just a boolean true/false, but a _proof_ that the element is indeed in the tree. A proof that `x` is in the tree `t` is either a proof that it is `here`, a proof that it is in the `left` subtree, or a proof that it is in the `right` subtree.

```
module Lookup {{_ : TDO A}} where

  data _∈_ {lower} {upper} (x : A) :
           (t : BST A lower upper) → Set where
    here  : ∀ {t₁ t₂} → x ≡ y  → x ∈ node y t₁ t₂
    left  : ∀ {t₁ t₂} → x ∈ t₁ → x ∈ node y t₁ t₂
    right : ∀ {t₁ t₂} → x ∈ t₂ → x ∈ node y t₁ t₂

```

The definition of `lookup` makes use of [`with`\-abstraction](https://agda.readthedocs.io/en/v2.6.0.1/language/with-abstraction.html) to inspect the result of the `tri` function on `x` and `y`.

```
  lookup : ∀ {lower} {upper}
         → (x : A) (t : BST A lower upper) → Maybe (x ∈ t)
  lookup x leaf = nothing
  lookup x (node y t₁ t₂) with tri x y
  ... | less    = mapMaybe left (lookup x t₁)
  ... | equal   = just (here it)
  ... | greater = mapMaybe right (lookup x t₂)

```

Similarly, we can define an insertion function. Here, we need to enforce the precondition that the element we want to insert is between the bounds (alternatively, we could have updated the bounds in the return type to ensure they include the inserted element).

```
module Insert {{_ : TDO A}} where

  insert : (x : A) (t : BST A lower upper)
         → {{l≤x : lower ≤ [ x ]}} {{x≤u : [ x ] ≤ upper}}
         → BST A lower upper
  insert x leaf = node x leaf leaf
  insert x (node y t₁ t₂) with tri x y
  ... | less    = node y (insert x t₁) t₂
  ... | equal   = node y t₁ t₂
  ... | greater = node y t₁ (insert x t₂)

```

To prove correctness of insertion, we have to show that `y ∈ insert x t` is equivalent to `x ≡ y ⊎ y ∈ t`. The proofs `insert-sound₂` and `insert-complete` are a bit long because there are two elements `x` and `y` that can both independently be `here`, in the left subtree, or in the right subtree, so we have to distinguish 9 distinct cases. Let me know if you manage to find a shorter proof!

```
  open Lookup

  insert-sound :
    (x : A) (t : BST A lower upper)
    → {{_ : lower ≤ [ x ]}} {{_ : [ x ] ≤ upper}}
    → (x ≡ y) ⊎ (y ∈ t) → y ∈ insert x t
  insert-sound x t (inl refl) = insert-sound₁ x t

    where

      insert-sound₁ :
        (x : A) (t : BST A lower upper)
        → {{_ : lower ≤ [ x ]}} {{_ : [ x ] ≤ upper}}
        → x ∈ insert x t
      insert-sound₁ x leaf = here refl
      insert-sound₁ x (node y t₁ t₂) with tri x y
      insert-sound₁ x (node y t₁ t₂) | less    = left (insert-sound₁ x t₁)
      insert-sound₁ x (node y t₁ t₂) | equal   = here it
      insert-sound₁ x (node y t₁ t₂) | greater = right (insert-sound₁ x t₂)

  insert-sound x t (inr y∈t) = insert-sound₂ x t y∈t

    where

      insert-sound₂ :
        (x : A) (t : BST A lower upper)
        → {{_ : lower ≤ [ x ]}} {{_ : [ x ] ≤ upper}}
        → y ∈ t → y ∈ insert x t
      insert-sound₂ x (node y t₁ t₂) (here  refl) with tri x y
      ... | less    = here refl
      ... | equal   = here refl
      ... | greater = here refl
      insert-sound₂ x (node y t₁ t₂) (left  y∈t₁) with tri x y
      ... | less    = left (insert-sound₂ x t₁ y∈t₁)
      ... | equal   = left y∈t₁
      ... | greater = left y∈t₁
      insert-sound₂ x (node y t₁ t₂) (right y∈t₂) with tri x y
      ... | less    = right y∈t₂
      ... | equal   = right y∈t₂
      ... | greater = right (insert-sound₂ x t₂ y∈t₂)

  insert-complete :
    (x : A) (t : BST A lower upper)
    → {{_ : lower ≤ [ x ]}} {{_ : [ x ] ≤ upper}}
    → y ∈ insert x t → (x ≡ y) ⊎ (y ∈ t)
  insert-complete x leaf           (here refl) = inl refl
  insert-complete x (node y t₁ t₂) y∈t'       with tri x y
  insert-complete x (node y t₁ t₂) (here refl)   | less    = inr (here refl)
  insert-complete x (node y t₁ t₂) (here refl)   | equal   = inl it
  insert-complete x (node y t₁ t₂) (here refl)   | greater = inr (here refl)
  insert-complete x (node y t₁ t₂) (left y∈t₁')  | less    = mapInr left (insert-complete x t₁ y∈t₁')
  insert-complete x (node y t₁ t₂) (left  y∈t₁)  | equal   = inr (left y∈t₁)
  insert-complete x (node y t₁ t₂) (left  y∈t₁)  | greater = inr (left y∈t₁)
  insert-complete x (node y t₁ t₂) (right y∈t₂)  | less    = inr (right y∈t₂)
  insert-complete x (node y t₁ t₂) (right y∈t₂)  | equal   = inr (right y∈t₂)
  insert-complete x (node y t₁ t₂) (right y∈t₂') | greater = mapInr right (insert-complete x t₂ y∈t₂')

```

Of course, there are many more functions on search trees we could want to implement and prove correct: deletion, merging, flattening … Likewise, there are other invariants we might want to enforce in the type, such as being well-balanced. I strongly recommend to read [Conor McBride’s paper](https://personal.cis.strath.ac.uk/conor.mcbride/Pivotal.pdf) on the topic, or try it yourself!