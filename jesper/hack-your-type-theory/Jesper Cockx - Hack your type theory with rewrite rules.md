Posted by Jesper on October 21, 2019

This is the first in a series of three blog posts on rewrite rules in Agda. In contrast to my [previous post](https://jesper.sikanda.be/posts/formalize-all-the-things.html), this post will decidedly _non-introductory_. Instead, we will have some fun by doing unsafe things and hacking things into the core reduction machinery of Agda.

The main part of this post will consist of several examples of how to use rewrite rules to go beyond the usual boundaries set by Agda and define your _own_ computation rules. The next two posts in this series will go more into how rewrite rules work in general and the metatheory of type theory extended with rewrite rules.

## Why rewrite rules?

The way I learned type theory from [Simon Thompson’s book](https://www.cs.kent.ac.uk/people/staff/sjt/TTFP/ttfp.pdf), each type former is defined by four sets of rules:

-   The **formation rule** (e.g. `Bool : Set`)
    
-   The **introduction rules** (e.g. `true : Bool` and `false : Bool`)
    
-   The **elimination rules** (e.g. if `P : Bool → Set`, `b : Bool`, `pt : P true`, and `pf : P false`, then `if b then pt else pf : P b`)
    
-   The **computation rules** (e.g. `if true then pt else pf = pt` and `if false then pt else pf = pf`)
    

Most of the time when we work in Agda, we don’t introduce new types by directly giving these rules. That would be very unsafe, as there’s no easy way for Agda to check that the given rules make sense. Instead, we can introduce new rules through _schemes_ that are well-known to be safe, such as strictly positive datatypes and terminating functions by dependent pattern matching.

However, if you’re experimenting with adding new features to dependently typed languages or if you’re a heavy user of them, you might find working within these schemes a bit too restrictive. You might be tempted to use `postulate` to define new types and terms, or to turn off the safety checks for termination, positivity, and/or universe consistency. Yet there is one thing that cannot be simply added by using these tricks. This is exactly the one thing that breathes life into the type theory: the computation rules. This is the purpose of _rewrite rules_ in Agda (as well as in some other languages like [Dedukti](https://deducteam.github.io/)): to allow the user of the language to extend the language’s notion of definitional equality with additional computation rules.

Concretely, given a proof (or a postulate) `p : ∀ x₁ ... xₙ → f u₁ ... uₙ ≡ v`, you can register it as a rewrite rule with a pragma `{-# REWRITE p #-}`. From this point on, Agda will automatically reduce instances of the left-hand side `f u₁ ... uₙ` (i.e. for specific values of `x₁ ... xₙ`) to the corresponding instance of `v`. To give a silly example, if `f : A → A` and `p : ∀ x → f x ≡ x`, then the rewrite rule will replace any application `f u` with `u`, effectively turning `f` into the identity function `λ x → x`.

There are some restrictions on what kind of equality proofs can be turned into rewrite rules, which I will go into more detail in the next post. Until then, I hope the examples in this post give a good idea of the kind of things that are possible.

One thing that is perhaps obvious but I want to stress nevertheless is that by design rewrite rules are a _very unsafe_ feature of Agda. Compared to using `postulate`, rewrite rules don’t allow you to break soundness (at least not directly), but they can break core assumptions of Agda such as confluence of reduction and even type preservation. So each time you use a rewrite rule, make sure you know it is justified, or be prepared to suffer the consequences.

With the introduction out of the way, let’s jump into some examples of cool things you can do with rewrite rules.

## Preliminaries

This whole post is written as a literate Agda file. As always, we some basic options and imports. For the purpose of this post, the two most important ones are the `--rewriting` flag and the import of `Agda.Builtin.Equality.Rewrite`, which are both required to make rewrite rules work. Meanwhile, the `--prop` flag enables Agda’s [`Prop` universe](https://agda.readthedocs.io/en/v2.6.0.1/language/prop.html) (new in Agda 2.6.0), which we will use in some of the examples.

```
{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

```

As in the previous post, I will make heavy use of [generalizable variables](https://agda.readthedocs.io/en/v2.6.0.1/language/generalization-of-declared-variables.html) to make the code more readable. (Honestly, I’m not sure how I ever managed to write Agda code without them.)

```
variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C       : Set ℓ
  P Q         : A → Set ℓ
  x y z       : A
  f g h       : (x : A) → P x
  b b₁ b₂ b₃  : Bool
  k l m n     : Nat
  xs ys zs    : List A

```

To avoid reliance on external libraries, we also need these two basic equality reasoning principles.

```
cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

transport : (P : A → Set ℓ) → x ≡ y → P x → P y
transport P refl p = p

```

## Example 1: Overlapping pattern matching

To start, let’s look at an example where rewrite rules can solve a problem that is encountered by almost every newcomer to Agda. This problem usually pops up as the question why `0 + m` computes to `m`, but `m + 0` does not (and similarly, `(suc m) + n` computes to `suc (m + n)` but `m + (suc n)` does not). This problem manifests for example when trying to prove commutativity of `_+_` (the lack of highlighting means the code does not typecheck):

```
+comm : m + n ≡ n + m
+comm {m = zero}  = refl
+comm {m = suc m} = cong suc (+comm {m = m})
```

Here, Agda complains that `n != n + zero of type Nat`. The usual way to solve this problem is by proving the equations `m + 0 ≡ m` and `m + (suc n) ≡ suc (m + n)` and using an explicit `rewrite` statement in the main proof (N.B.: Agda’s `rewrite` keyword should not be confused with rewrite rules, which are added by a `REWRITE` pragma. Confusing, I know.)

This problem is something that has both frustrated and fascinated me from the very beginning I started working on type theory. During my master thesis, I worked on adding [_overlapping computation rules_](https://jesper.sikanda.be/files/overlapping-and-order-independent-patterns.pdf) to make this problem go away _without_ adding any explicit `rewrite` statements to the proof above.

By using rewrite rules, we can simulate the solution from our paper. First, we need to prove that the equations we want hold as _propositional equalities_:

```
zero+ : zero + n ≡ n
zero+ = refl

suc+ : (suc m) + n ≡ suc (m + n)
suc+ = refl

+zero : m + zero ≡ m
+zero {m = zero}  = refl
+zero {m = suc m} = cong suc +zero

+suc : m + (suc n) ≡ suc (m + n)
+suc {m = zero}  = refl
+suc {m = suc m} = cong suc +suc

```

We mark the equalities that are not already definitional as rewrite rules with a `REWRITE` pragma:

```
{-# REWRITE +zero +suc #-}

```

Now the proof of commutativity works exactly as we wrote before:

```
+comm : m + n ≡ n + m
+comm {m = zero}  = refl
+comm {m = suc m} = cong suc (+comm {m = m})

```

Note that there is **no** way to make this proof go through without rewrite rules: it is essential that `_+_` computes both on its first and second arguments, but there’s no way to define `_+_` in such a way using Agda’s regular pattern matching.

## Example 2: New equations for neutral terms

The idea of extending existing functions with new computation rules has been taken much further in a very nice paper by Guillaume Allais, Conor McBride, and Pierre Boutillier titled [New Equations for Neutral Terms](https://arxiv.org/abs/1304.0809). In this paper, they add new computation rules to classic functions on lists such as `map`, `_++_`, and `fold`. In Agda, we can prove these rules and then add them as rewrite rules (here I only show a subset of the rules in the paper):

```
map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

infixr 5 _++_
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map-id : map (λ x → x) xs ≡ xs
map-id {xs = []}     = refl
map-id {xs = x ∷ xs} = cong (_∷_ x) map-id

map-fuse : map f (map g xs) ≡ map (λ x → f (g x)) xs
map-fuse {xs = []}     = refl
map-fuse {xs = x ∷ xs} = cong (_∷_ _) map-fuse

map-++ : map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
map-++ {xs = []}     = refl
map-++ {xs = x ∷ xs} = cong (_∷_ _) (map-++ {xs = xs})

{-# REWRITE map-id map-fuse map-++ #-}

```

These rules look reasonably simple, but when used together they can be quite powerful. For example, below we show that the expression `map swap (map swap xs ++ map swap ys)` reduces directly to `xs ++ ys`, without doing any induction on the lists!

```
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

swap : A × B → B × A
swap (x , y) = y , x

test₁ : map swap (map swap xs ++ map swap ys) ≡ xs ++ ys
test₁ = refl

```

To compute the left-hand side of the equation to the right-hand side, Agda makes use of `map-++` (`step₁`), `map-fuse` (`step₂`), built-in eta-equality (`step₃`), the definition of `swap` (`step₄`), and finally the `map-id` rewrite rule (`step₅`).

```
-- Using map-++:
step₁ : map swap (map swap xs ++ map swap ys)
      ≡ map swap (map swap xs) ++ map swap (map swap ys)
step₁ = refl

-- Using map-fuse (likewise for ys)
step₂ : map swap (map swap xs)
      ≡ map (λ x → swap (swap x)) xs
step₂ = refl

-- Using eta-expansion
step₃ : map (λ x → swap (swap x)) xs
      ≡ map (λ x → swap (swap (fst x , snd x))) xs
step₃ = refl

-- Using definition of swap (2x)
step₄ : map (λ x → swap (swap (fst x , snd x))) xs
      ≡ map (λ x → (fst x , snd x)) xs
step₄ = refl

-- Using map-id (together with eta-contraction)
step₅ : map (λ x → (fst x , snd x)) xs ≡ xs
step₅ = refl

```

## Example 3: Higher inductive types

The original motivation for adding rewrite rules to Agda had little to do with overlapping computation rules as in the previous examples. Instead, its purpose was to experiment with defining [_higher inductive types_](https://homotopytypetheory.org/book/). In particular, it was meant as an alternative for people using [clever (but horrible) hacks](https://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/) to make their higher inductive types compute.

A higher inductive type is like a regular inductive type `D` with some additional _path constructors_, which construct an element of the identity type `a ≡ b` where `a : D` and `b : D`. A classic example is the `Circle` type, which has one regular constructor `base` and one path constructor `loop`:

```
postulate
  Circle : Set
  base : Circle
  loop : base ≡ base

postulate
  Circle-elim : (P : Circle → Set ℓ)
    → (base* : P base)
    → (loop* : transport P loop base* ≡ base*)
    → (x : Circle) → P x
  elim-base : ∀ (P : Circle → Set ℓ) base* loop*
    → Circle-elim P base* loop* base ≡ base*
{-# REWRITE elim-base #-}

```

To specify the computation rule for `Circle-elim` applied to `loop`, we need the dependent version of `cong`, which is called `apd` in the book.

```
apd : (f : (x : A) → P x) (p : x ≡ y)
    → transport P p (f x) ≡ f y
apd f refl = refl

postulate
  elim-loop : ∀ (P : Circle → Set ℓ) base* loop*
    → apd (Circle-elim P base* loop*) loop ≡ loop*
{-# REWRITE elim-loop #-}

```

Interestingly, the type of `elim-loop` is not even well-formed unless we alreay have `elim-base` as a rewrite rule! So without rewrite rules, it is even difficult to _state_ the computation rule of `Circle-elim` for `loop`.

## Example 4: Quotient types

One of the well-known weak spots of intentional type theory is the poor handling of quotient types. One of the more promising attempts at adding quotients to Agda is by [Guillaume Brunerie in the initiality project](https://github.com/guillaumebrunerie/initiality/blob/reflection/quotients.agda), which uses a combination of rewrite rules and Agda’s new (strict) `Prop` universe.

Before I can give the definition of the quotient type, we first need to define the `Prop`\-valued equality type `_≐_`. We also define its corresponding notion of `transport`, which has to be postulated due to current limitations in the implementation of `Prop`. Luckily, we can actually make `transportR` compute in the expected way by postulating the expected computational behaviour and turning it into a rewrite rule.

```
data _≐_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

postulate
  transportR : (P : A → Set ℓ) → x ≐ y → P x → P y
  transportR-refl : transportR P refl x ≡ x
{-# REWRITE transportR-refl #-}

```

Now we can define the quotient type `_//_`. Specifically, given a type `A` and a `Prop`\-valued relation `R : A → A → Prop`, we construct the type `A // R` consisting of elements `proj x` where `x : A` and `proj x ≡ proj y` if and only if `R x y`.

```
variable
  R : A → A → Prop

postulate
  _//_    : (A : Set ℓ) (R : A → A → Prop) → Set ℓ
  proj    : A → A // R
  quot    : R x y → proj {R = R} x ≐ proj {R = R} y

```

The crucial element here is the elimination principle `//-elim`, which allows us to define functions that _extract_ an element of `A` from a given element of `A // R`, as long as we have a _proof_ `quot*` that the function behaves the same on `proj x` and `proj y` whenever `R x y` holds. The computation rule `//-beta` turns this definition of quotients into more than just a static blob of postulates by allowing `//-elim` to compute when it is applied to a `proj x`.

```
  //-elim : (P : A // R → Set ℓ)
    → (proj* : (x : A) → P (proj x))
    → (quot* : {x y : A} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → (x : A // R) → P x
  //-beta : {R : A → A → Prop} (P : A // R → Set ℓ)
    → (proj* : (x : A) → P (proj x))
    → (quot* : {x y : A} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → {u : A} → //-elim P proj* quot* (proj u) ≡ proj* u
  -- Note: The type of //-beta mysteriously does not
  -- check when I leave out the {R : A → A → Prop},
  -- I'm not sure what's up with that.
{-# REWRITE //-beta #-}

```

(As a side note, [here](https://github.com/coq/coq/issues/10871) is an interesting recent discussion on quotient types in Lean, Coq, and Agda.)

## Example 5: Exceptional type theory

I have a secret to share with you: my first programming language was Java. While I don’t miss most parts of it, sometimes I just long to use a good unchecked exception in my pristine purely functional language. Luckily, my friends over at Inria in Nantes have written the aptly named paper [Failure is Not an Option: An Exceptional Type Theory](https://hal.inria.fr/hal-01840643/document), which shows how to add exceptions to Coq. Through the exceptional power of rewrite rules, we can also encode their system in Agda.

First, we postulate a type `Exc` with any kinds of exceptions we might want to use (here we just have `runtimeException` for simplicity). We then add the possibility to `raise` an exception, producing an element of an arbitrary type `A`.

```
postulate
  Exc : Set
  runtimeException : Exc
  raise : Exc → A

```

By adding the appropriate rewrite rules for each type former, we can ensure that exceptions are _propagated_ to the top-level. Below, I give two examples. For positive types such as `Nat`, exceptions are propagated _outwards_, while for negative types such as function types, exceptions are propagated _inwards_.

```
  raise-suc : {e : Exc} → suc (raise e) ≡ raise e

  raise-fun : {e : Exc}
    → raise {A = (x : A) → P x} e
    ≡ λ x → raise {A = P x} e

{-# REWRITE raise-suc raise-fun #-}

```

To complete the system, we can then add the ability to `catch` exceptions at specific types. This takes the shape of an eliminator with one additional method for handling the case where the element under scrutiny is of the form `raise e`.

```
postulate
  catch-Bool : (P : Bool → Set ℓ)
               (pt : P true) (pf : P false)
               (h : ∀ e → P (raise e))
             → (b : Bool) → P b

  catch-true  : ∀ (P : Bool → Set ℓ) pt pf h
              → catch-Bool P pt pf h true ≡ pt
  catch-false : ∀ (P : Bool → Set ℓ) pt pf h
              → catch-Bool P pt pf h false ≡ pf
  catch-exc   : ∀ (P : Bool → Set ℓ) pt pf h e
              → catch-Bool P pt pf h (raise e) ≡ h e

{-# REWRITE catch-true catch-false catch-exc #-}

```

In their paper, Pierre-Marie and Nicolas show how to build a _safe_ version of exceptions on top of this system, using _parametricity_ to enforce that all exceptions are caught locally. Please go read their paper if you want to know more!

## Example 6: Observational equality

We can go even further in extending our type theory with new concepts using rewrite rules. For example, we can define _type constructors_ that compute according to the type they are applied to. This is the core concept of [_observational type theory_](http://strictlypositive.org/ott.pdf) (OTT). OTT extends type theory with an observational equality type (here called `_≅_`) that computes acoording to the type of the elements being compared. For example, an equality proof of type `(a , b) ≅ (c , d)` **is** a pair of proofs, one of type `a ≅ c` and one of type `b ≅ d`.

OTT had a strong influence on the recent development of cubical type theory, which extends it with a _proof-relevant_ notion of equality. Yet there are still some things that are possible in OTT but not in cubical, so we should not write it off yet. For example, OTT has _definitional proof irrelevance_, while it is not clear yet how this can be integrated into cubical (although [XTT](https://arxiv.org/abs/1904.08562) looks very promising).

Below, I define a small fragment of OTT by using rewrite rules in Agda. Since OTT has a proof-irrelevant equality type, I use Agda’s `Prop` to get the same effect.

First, we need some basic types in `Prop`:

```
record ⊤ {ℓ} : Prop ℓ where constructor tt

data   ⊥ {ℓ} : Prop ℓ where

record _∧_ (X : Prop ℓ₁) (Y : Prop ℓ₂) : Prop (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : X
    snd : Y
open _∧_

```

The central type is observational equality `_≅_`, which should compute according to the types of the elements being compared. Here I give the computation rules for `Bool` and for function types:

```
infix 6 _≅_
-- Observational equality
postulate
  _≅_ : {A : Set ℓ₁} {B : Set ℓ₂} → A → B → Prop (ℓ₁ ⊔ ℓ₂)

HEq = _≅_
syntax HEq {A = A} {B = B} x y = x ∈ A ≅ y ∈ B

postulate
  refl-Bool   : (Bool  ≅ Bool)  ≡ ⊤
  refl-true   : (true  ≅ true)  ≡ ⊤
  refl-false  : (false ≅ false) ≡ ⊤
  conflict-tf : (true  ≅ false) ≡ ⊥
  conflict-ft : (false ≅ true)  ≡ ⊥
{-# REWRITE refl-Bool refl-true refl-false
            conflict-tf conflict-ft #-}

postulate
  cong-Π : ((x : A) → P x) ≅ ((y : B) → Q y)
         ≡ (B ≅ A) ∧ ((x : A)(y : B) → y ≅ x → P x ≅ Q y)
  cong-λ : {A : Set ℓ₁} {B : Set ℓ₂}
    → {P : A → Set ℓ₃} {Q : B → Set ℓ₄}
    → (f : (x : A) → P x) (g : (y : B) → Q y)
    → ((λ x → f x) ≅ (λ y → g y))
    ≡ ((x : A) (y : B) (x≅y : x ≅ y) → f x ≅ g y)
{-# REWRITE cong-Π cong-λ #-}

```

To be able to actually reason about equality, OTT also has two more notions: **coercion** and **cohesion**. Coercion allows us to cast an element from one type to the other when we know both types are equal, and cohesion allows us to prove that coercion is computationally a no-op.

```
infix 10 _[_⟩ _||_

postulate
  _[_⟩    : A → A ≅ B → B         -- Coercion
  _||_    : (x : A) (Q : A ≅ B)
          → x ∈ A ≅ x [ Q ⟩ ∈ B   -- Coherence

```

Again, we need more rewrite rules to make sure coercion computes in the right way when applied to specific type constructors. Note that we _don’t_ need rewrite rules for coherence, since the result is of type `_ ≅ _` which is a `Prop`, so it anyway has no computational content.

Coercing an element from `Bool` to `Bool` is easy.

```
postulate
  coerce-Bool : b [ tt ⟩ ≡ b
{-# REWRITE coerce-Bool #-}

```

(Note that `Bool ≅ Bool` computes to `⊤`, so any proof of it will be equal to `tt` by eta-equality.)

To coerce a function from `(x : A) → P x` to `(y : B) → Q y` we need to:

1.  Coerce the input from `y : B` to `x : A`
2.  Apply the function to get an element of type `P x`
3.  Coerce the output back to an element of `Q y`

In the last step, we need to use coherence to show that `x` and `y` are (heterogeneously) equal.

```
postulate
  coerce-Π : {A : Set ℓ₁} {B : Set ℓ₂}
    → {P : A → Set ℓ₃} {Q : B → Set ℓ₄}
    → {f : (x : A) → P x}
    → (ΠAP≅ΠBQ : ((x : A) → P x) ≅ ((y : B) → Q y))
    → _≡_ {A = (y : B) → Q y} (f [ ΠAP≅ΠBQ ⟩) λ (y : B) →
        let B≅A : B ≅ A
            B≅A = fst ΠAP≅ΠBQ
            x   : A
            x   = y [ B≅A ⟩
            Px≅Qy : P x ≅ Q y
            Px≅Qy = snd ΠAP≅ΠBQ x y (_||_ {B = A} y B≅A)
        in f x [ Px≅Qy ⟩
{-# REWRITE coerce-Π #-}

```

Of course this is just a fragment of the whole system, but implementing all of OTT would go beyond the scope of this blog post. Hopefully this at least gives an idea how one could implement the full system.

## Conclusion

With all these examples, I think this blog post has become long enough. If you read all the way to here, I hope you found at least one example that gave you the itch to try rewrite rules yourself. Be sure to let me know if you come up with other cool examples! And if you got interested in the exact workings of rewrite rules in Agda and how they are implemented, stay tuned for the next post in this series.