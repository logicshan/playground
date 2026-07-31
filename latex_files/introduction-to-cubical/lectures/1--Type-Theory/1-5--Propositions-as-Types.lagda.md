<!--
```
module 1--Type-Theory.1-5--Propositions-as-Types where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
```
-->


# Lecture 1-5: Propositions as Types

In the previous lectures we saw how to define some familiar data types
--- Booleans, natural numbers, integers --- and how to define some of
their familiar operations. But to do mathematics, we need to be able
to prove things about these types.

One way to formalize a proposition is as an element of the Booleans.
We've already seen several functions into the Booleans, like
``isEven``, ``isWeekend``, ``isLeft``, and so on. This way of
representing propositions is common in other programming languages,
but there is another, more powerful way of formalizing propositions
which is made possible by dependent types: we think of types as
themselves expressing propositions.

A proposition, informally speaking, is a mathematical statement for
which we know what would constitute a proof. To prove that 6 is even,
for example, we could divide it evenly. The statement "6 is even" is a
thus a proposition: we know what it would mean to prove it. Proving
that that a day `d` is on a weekend would mean showing that `d` is
Saturday or Sunday, so "`d` is on a weekend" is also a proposition,
this time a proposition about an unspecified element `d`.

This notion of proposition remains sensible when the thing we want to
prove is not actually true: a proof that 7 is even would also consist
of a demonstration that we can divide it evenly into two whole
numbers, but this time we can't actually achieve that goal.

In this lecture, we give a first pass at a type theoretic notion of
proposition, something we will refine later in Lecture 2-7.


## Propositions as Types

The core of the idea is that a proposition will be encoded as a type,
and to prove the proposition will be to give an element of that type.

First, we have type versions of ``true`` and ``false``.

```
TrueP : Type
TrueP = ⊤

FalseP : Type
FalseP = ∅
```

The type ``⊤`` has an element ``tt``; under the interpretation that
proofs of propositions are the elements of the types representing
those propositions, this means we can prove that ``TrueP`` holds. On
the other hand, ``∅`` has no elements, and therefore we can't prove
that ``FalseP`` holds --- at least, not without assuming some
contradictory hypotheses.

We can turn each Boolean value into its corresponding type:

```
IsTrue : Bool → Type
IsTrue true  = TrueP
IsTrue false = FalseP
```

An amazing feature of propositions-as-types idea is that many of the
operations on types we have seen in the last few lectures become
familiar operations on propositions.

In ordinary logic, to prove `P and Q` we need to prove `P` and to
prove `Q`. That is, a proof of `P and Q` consists of a pair of proofs,
one for `P` and one for `Q`. We can turn this directly into a
definition.

```
_andP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
P andP Q = P × Q
```

Now consider implication. Implication means that, assuming you have a
proof of `P`, you can get a proof of `Q`. This is exactly what
functions do, so we can also turn this into a definition:

```
_impliesP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
P impliesP Q = P → Q
```

Once we have these as building blocks, we can start to construct other
logical operations. When two propositions imply each other, we say
that they are *logically equivalent*:

```
_iffP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
P iffP Q = (P → Q) × (Q → P)
```

As a sanity check, we can show that these operations on types
correspond correctly with the analogous operations on Booleans via
``IsTrue``. Prove the following by case-splitting on the arguments and
filling in both sides of the logical equivalence. On the left of the
``iffP`` we use the ordinary operation on Booleans, and on the right
we use the corresponding operation on propositions-as-types.

The complicated goal below gives us an opportunity to introduce
another handy Agda trick: splitting on the *goal*, rather than an
argument. This works when the current goal is a negative type, such as
`→` or ``×``, which it is in this case. Type `C-c C-c`, the same
keybinding as case splitting, but this time don't provide the name of
variable to split on. Because Agda knows that the goal has type `×`,
this will result in two copattern matching lines, one for the first
component and one for the second component. Splitting the goal again
in each of these will give you an `x` argument, because the goal in
both cases is a `→` type. Doing this can help keep things organised,
rather than piling everything onto the right-hand side of the `=`
sign. (At some point you will also have to pattern match on the
Boolean arguments.)

```
and→Type : (a b : Bool) → (IsTrue (a and b)) iffP ((IsTrue a) andP (IsTrue b))
-- aka:
-- and→Type : (a b : Bool) → ((IsTrue (a and b)) → (IsTrue a × IsTrue b))
--                         × ((IsTrue a × IsTrue b) → IsTrue (a and b))
-- Exercise:
and→Type true true   = (λ _ → tt , tt) , λ _ → tt
and→Type true false  = (λ ()) , λ ()
and→Type false true  = (λ ()) , λ ()
and→Type false false = (λ ()) , λ ()

implies→Type : (a b : Bool) → (IsTrue (a implies b)) iffP ((IsTrue a) impliesP (IsTrue b))
-- aka:
-- implies→Type : (a b : Bool) → ((IsTrue (a implies b)) → (IsTrue a → IsTrue b))
--                             × ((IsTrue a → IsTrue b) → (IsTrue (a implies b)))
-- Exercise:
implies→Type true true = (λ _ _ → tt) , λ _ → tt
implies→Type true false = (λ ()) , λ x → x tt
implies→Type false true = (λ _ ()) , λ _ → tt
implies→Type false false = (λ _ ()) , λ _ → tt
```

We interpret negation as a special case of implication: "not P" is the
same as "P implies false", and again we make this our definition.

```
¬_ : {ℓ : Level} → Type ℓ → Type ℓ
¬_ P = P → ∅

-- This makes `¬` go on the outside of most formulas
infix 3 ¬_
```

We had better also make sure this means what we think it does!

```
not→Type : (a : Bool) → (IsTrue (not a)) iffP (¬ IsTrue a)
-- Exercise:
not→Type true = ∅-rec , λ x → x tt
not→Type false = (λ _ ()) , λ _ → tt
```

A basic principle of negation is contraposition: if `P` implies `Q`
then whenever `Q` is false, certainly `P` must be false too.

This gives us an opportunity to introduce another useful Agda hotkey.
If you place your cursor in the below hole and press `C-c C-,` (that
is, control-c, control-comma), Agda will tell you that the goal has
type `¬ Q → ¬ P`. This is true, but the path forwards is a little
obscured. It helps if we *unfold* the definition of ``¬`` in the goal.
We can ask Agda to do this by prefixing the command with `C-u C-u`,
which asks Agda to simplify the expression more aggressively. (Yes,
these key-bindings are a bit silly.)

So, in the goal below, `C-u C-u C-c C-,` reveals that the goal has
type `(Q → ∅) → P → ∅`. This makes it clear that ``¬-contra`` should
take two arguments, one with type `Q → ∅`, and the other with type
`P`.

```
¬-contra : {ℓ ℓ' : Level} → {P : Type ℓ} → {Q : Type ℓ'}
  → (P → Q)
  → (¬ Q → ¬ P)
-- Exercise:
¬-contra f = λ ¬q p → ¬q (f p)
```

The logic of propositions-as-types is not exactly the same as the
logic of Booleans, however. The reason has to do with double negation:
recall that for the Booleans, `not (not b)` is always equal to `b`,
which you can check by just trying both possibilities. Working with
propositions-as-types, we can show one direction of that equivalence:

```
implies¬¬ : {ℓ : Level} → {P : Type ℓ} 
  → (P → (¬ ¬ P))
-- Exercise:
implies¬¬ p = λ ¬p → ¬p p
```

But, we cannot show that `¬ ¬ A → A` in general!

```
-- Uncomment to try if you want!
-- impossible-¬¬implies : {ℓ : Level} (P : Type ℓ) → (¬ ¬ P) → P
-- impossible-¬¬implies P nnp = {!!}
```

One way to understand the difference between `¬ ¬ P` and `P` is that
we think of `p : P` as giving *evidence* that the proposition `P`
holds. What `¬ ¬ P` says is that to assume `P` were false would lead
to a contradiction. Certainly, if we already have evidence for `P`,
then the claim that `P` is also false leads to a contradiction, this
is the ``implies¬¬`` fact we just proved above.

But `¬ ¬ P` does not on its own conjure any direct evidence for `P`.
This quirk of logic in type theory makes it a *constructive* logic ---
there is a difference between providing (or "constructing") evidence
for a proposition and proving that its falsehood would be absurd ---
as opposed to the "classical" logic of the Booleans.

It seems that we're at risk of `¬`s piling up endlessly if the above
implication only works in one direction. But in fact, as soon as we
have three `¬`s, we can cancel two of them.

```
¬¬¬implies¬ : {ℓ : Level} → {P : Type ℓ} 
  → (¬ ¬ ¬ P) → (¬ P)
-- Exercise:
¬¬¬implies¬ nnnp = λ p → nnnp λ np → np p
```

As a challenge, prove that it's impossible for `P` and `¬ P` to be
logically equivalence. Again, it may help to see what to do next if
you unfold the definitions.

```
¬-not-same : {ℓ : Level} → {P : Type ℓ} 
  → ¬ (P iffP (¬ P))
-- Exercise: 
¬-not-same (l , r) = l (r (λ x → l x x)) (r (λ x → l x x))
```


## Or

This pattern of relating logical operations to type operations
continues with ``or`` but runs into a subtle hiccup. Our first
attempt at a type avatar of ``or`` is ``⊎``, the disjoint union. This
makes some sense: to prove `P or Q` should consist of either a proof
of `P` or a proof of `Q`.

First, let's define maps both ways.

```
or→Type-fro : (a b : Bool) → (IsTrue a ⊎ IsTrue b) → IsTrue (a or b)
-- Exercise:
or→Type-fro true true _ = tt
or→Type-fro true false _ = tt
or→Type-fro false true _ = tt
or→Type-fro false false (inl ())
or→Type-fro false false (inr ())

or→Type-to : (a b : Bool) → IsTrue (a or b) → (IsTrue a ⊎ IsTrue b)
-- Exercise:
or→Type-to true true p = inl p
or→Type-to true false p = inl p
or→Type-to false true p = inr p
or→Type-to false false ()
```

What this shows is that `IsTrue (a or b)` and `(IsTrue a) ⊎ (IsTrue b)`
are logically equivalent, that is, one ``iffP`` the other. But
now: define the map backwards again, but making the opposite choice in
the case `or→Type-to' true true`.

```
or→Type-to' : (a b : Bool) → IsTrue (a or b) → ((IsTrue a) ⊎ (IsTrue b))
-- Exercise:
or→Type-to' true true p = inr p
or→Type-to' true false p = inl p
or→Type-to' false true p = inr p
or→Type-to' false false ()
```

So having an element of `(IsTrue a) ⊎ (IsTrue b)`, is *more*
information than simply knowing that at least one of `a` or `b` is
true: if *both* `a` and `b` are true, the element of `(IsTrue a) ⊎
(IsTrue b)` has to make a choice between the two sides. So, the type
no longer merely expresses the truth of a proposition.

What we ought to learn from this is that not *every* type should be
thought of as a proposition. Some types, like ``ℕ``, say, are better
thought of as sets that have many different elements. What we are
noticing with ``or`` is that the disjoint union of two propositions
can contain a non-trivial amount of information. We actually saw this
earlier, when we proved that ``Bool`` is bijective with `⊤ ⊎ ⊤`.

This is the refinement that we will eventually make in Lecture 2-7, to
pick out which types are the ones we should think of as propositions:
types that have at most one element. This unique element, if it exists
at all, is thought of as "the fact that the proposition is true". At
that point we will also properly define the operation which
corresponds to the proposition `P or Q`.

Nevertheless, ``⊎`` is close enough to ``or`` for our
current purposes. Try proving De Morgan's laws, which may be
familiar from ordinary propositional logic. For the last one, we get
stuck in a similar way to `impossible-¬¬implies` above. In that case,
how are we supposed to know which of ``inl`` or ``inr`` to
pick?

```
DeMorgan-law-1 : {P Q : Type} → ¬ (P ⊎ Q) → (¬ P) × (¬ Q)
-- Exercise:
DeMorgan-law-1 npq .fst = npq ∘ inl -- λ p → npq (inl p)
DeMorgan-law-1 npq .snd = npq ∘ inr -- λ q → npq (inr q)

DeMorgan-law-2 : {P Q : Type} → (¬ P) × (¬ Q) → ¬ (P ⊎ Q)
-- Exercise:
DeMorgan-law-2 (np , _) (inl p) = np p
DeMorgan-law-2 (_ , nq) (inr q) = nq q

DeMorgan-law-3 : {P Q : Type} → (¬ P) ⊎ (¬ Q) → ¬ (P × Q)
-- Exercise:
DeMorgan-law-3 (inl np) (p , _) = np p
DeMorgan-law-3 (inr nq) (_ , q) = nq q

-- Uncomment to see where you get stuck if you want!
-- impossible-DeMorgan-law-4 : {P Q : Type} → ¬ (P × Q) → (¬ P) ⊎ (¬ Q)
-- impossible-DeMorgan-law-4 npq = {!!}
```


## Equality

The most fundamental proposition concerning the data types we have
seen so far is *equality*. We can define equality for Booleans
by case-splitting as follows:

```
_≡Bool_ : (a b : Bool) → Type
true  ≡Bool true  = ⊤
true  ≡Bool false = ∅
false ≡Bool true  = ∅
false ≡Bool false = ⊤
```

That is, there is a unique proof that `true ≡Bool true`, no proofs
that `true ≡Bool false`, and so on. This kind of equality defined by
pattern matching is often called "observational" equality.

Now how do we prove an equality of ``Bool``s? We just inhabit the
relevant type:

```
true-equals-true : true ≡Bool true
true-equals-true = tt
```

What if the Boolean value involved is a variable, or some complicated
expression? By case splitting, we can hopefully simplify the goal into
one of the trivial cases as above, that is, we just do recursion on
the data type! (Using recursion to prove a proposition is often called
"induction", we will make this more precise in the next section.)

Here's an example. With this notion of equality, every ``Bool`` is
either equal to ``true`` or to ``false``. This is the Law of Excluded
Middle for Booleans logic; there is no middle option!

```
≡Bool-LEM : (a : Bool) → (a ≡Bool true) ⊎ (a ≡Bool false)
≡Bool-LEM true = inl tt
≡Bool-LEM false = inr tt
```

By pattern matching, we can prove that observational equality is a
reflexive, symmetric, and transitive relation on Booleans.

```
≡Bool-refl : (a : Bool) → a ≡Bool a
-- Exercise:
≡Bool-refl true = tt
≡Bool-refl false = tt

≡Bool-sym : (a b : Bool)
  → a ≡Bool b
  → b ≡Bool a
-- Exercise:
≡Bool-sym true true _ = tt
≡Bool-sym true false ()
≡Bool-sym false true ()
≡Bool-sym false false _ = tt

≡Bool-trans : (a b c : Bool)
  → a ≡Bool b
  → b ≡Bool c
  → a ≡Bool c
-- Exercise:
≡Bool-trans true true _ _ q = q
≡Bool-trans true false _ ()
≡Bool-trans false true _ ()
≡Bool-trans false false _ _ q = q
```

We can also show that all of our logical operations preserve the
relation of equality, as expected. Like the previous, these can be
proven purely by splitting into all the possible cases, so we won't
make you do them all.

```
not-≡Bool : (a b : Bool)
  → a ≡Bool b
  → (not a) ≡Bool (not b)
not-≡Bool true true _ = tt
not-≡Bool true false ()
not-≡Bool false true ()
not-≡Bool false false _ = tt

and-≡Bool : (a1 a2 b1 b2 : Bool)
  → (a1 ≡Bool a2)
  → (b1 ≡Bool b2)
  → (a1 and b1) ≡Bool (a2 and b2)
and-≡Bool true true true true _ _ = tt
and-≡Bool true true true false _ ()
and-≡Bool true true false true _ ()
and-≡Bool true true false false _ _ = tt
and-≡Bool true false _ _ ()
and-≡Bool false true _ _ ()
and-≡Bool false false _ _ _ _ = tt
```

We can similarly define equality of natural numbers.

```
_≡ℕ_ : (n m : ℕ) → Type

zero  ≡ℕ zero  = ⊤
zero  ≡ℕ suc m = ∅
suc n ≡ℕ zero  = ∅
suc n ≡ℕ suc m = n ≡ℕ m

infix 4 _≡ℕ_
```

And show that it is a reflexive, symmetric, and transitive relation.
The difference in the proofs is that because ``ℕ`` is a
recursive datatype, some of the cases in the proofs will need to be recursive
too.

```
≡ℕ-refl : (n : ℕ) → n ≡ℕ n
-- Exercise:
≡ℕ-refl zero = tt
≡ℕ-refl (suc n) = ≡ℕ-refl n

≡ℕ-sym : (n m : ℕ)
  → n ≡ℕ m
  → m ≡ℕ n
-- Exercise:
≡ℕ-sym zero zero _ = tt
≡ℕ-sym zero (suc _) ()
≡ℕ-sym (suc _) zero ()
≡ℕ-sym (suc n) (suc m) p = ≡ℕ-sym n m p

≡ℕ-trans : (n m k : ℕ)
  → n ≡ℕ m
  → m ≡ℕ k
  → n ≡ℕ k
-- Exercise:
≡ℕ-trans zero zero _ _ q = q
≡ℕ-trans zero (suc _) _ ()
≡ℕ-trans (suc _) zero _ ()
≡ℕ-trans (suc _) (suc _) zero p ()
≡ℕ-trans (suc n) (suc m) (suc k) p q = ≡ℕ-trans n m k p q
```

Next, we can show that addition is unital (that is, has an identity
element), and associative. These are all very easy by recursion.
Remember that you don't *have* to case split on an argument just
because you can, ``+ℕ-assoc`` is much simpler if you don't!

```
+ℕ-≡ℕ-idl : (n : ℕ) → (zero +ℕ n) ≡ℕ n
-- Exercise:
+ℕ-≡ℕ-idl zero = tt
+ℕ-≡ℕ-idl (suc n) = +ℕ-≡ℕ-idl n

+ℕ-≡ℕ-idr : (n : ℕ) → (n +ℕ zero) ≡ℕ n
-- Exercise:
+ℕ-≡ℕ-idr zero = tt
+ℕ-≡ℕ-idr (suc n) = +ℕ-≡ℕ-idr n

+ℕ-≡ℕ-assoc : (n m k : ℕ) → (n +ℕ (m +ℕ k)) ≡ℕ ((n +ℕ m) +ℕ k)
-- Exercise:
+ℕ-≡ℕ-assoc zero m k = ≡ℕ-refl (m +ℕ k)
+ℕ-≡ℕ-assoc (suc n) m k = +ℕ-≡ℕ-assoc n m k
```

Finally, we can show that addition is commutative. This one is
trickier, and we will have to glue together some of the facts we
proved above. In both parts, it is easiest if you *don't* pattern
match on both arguments.

```
+ℕ-≡ℕ-comm-helper : (n m : ℕ) → (n +ℕ (suc m)) ≡ℕ suc (n +ℕ m)
-- Exercise:
+ℕ-≡ℕ-comm-helper zero m = ≡ℕ-refl m
+ℕ-≡ℕ-comm-helper (suc n) m = +ℕ-≡ℕ-comm-helper n m

+ℕ-≡ℕ-comm : (n m : ℕ) → (n +ℕ m) ≡ℕ (m +ℕ n)
-- Exercise:
+ℕ-≡ℕ-comm zero m = ≡ℕ-sym (m +ℕ zero) m (+ℕ-≡ℕ-idr m)
+ℕ-≡ℕ-comm (suc n) m = 
  ≡ℕ-trans (suc (n +ℕ m)) (suc (m +ℕ n)) (m +ℕ suc n)
    (+ℕ-≡ℕ-comm n m)
    (≡ℕ-sym (m +ℕ suc n) (suc (m +ℕ n)) (+ℕ-≡ℕ-comm-helper m n))
```

It would be tedious if we had to define the specific notion of
equality we wanted for every type that we ever define. It's also not
entirely exactly how to do it in more difficult cases.

For example, to say that elements in the disjoint union `A ⊎ B` are
equal, we would want to say that if `a = a'` then `inl a = inl a'` and
if `b = b'` then `inr b = inr b'`, and that it is never the case that
`inl a = inr b` since the union is disjoint. But
without knowing specifically what the types `A` and `B` are, we
don't know what equality means for them.

Remarkably, it is possible to give a uniform notion of "equality" for
any type --- this is the subject of Part 2 of these notes. As
we'll see shortly, this general notion of *paths* between of elements
of general types will not always be a proposition --- paths will often
be interesting pieces of data in their own right.


## Induction Principles

In the above proofs we were secretly using an upgraded form of the
recursion principles for ``Bool`` and ``ℕ`` known as "induction
principles". The difference is that where recursion principles allowed
us to define ordinary functions out of ``Bool``, ``ℕ``, etc.,
induction principles allow us to define *dependent* functions out of
these types into a type family of our choosing.

``Bool`` is the easiest. Here a type family `C : Bool → Type ℓ`,
simply picks out two (possibly different) types, `C true` and `C
false`. The recursion principle is upgraded to use one element of each
of these types rather than two elements of the same type:

```
Bool-ind : {ℓ : Level}
  → {C : Bool → Type ℓ}
  → C true
  → C false
  → ((x : Bool) → C x)
-- Exercise:
Bool-ind c₁ c₂ true = c₁
Bool-ind c₁ c₂ false = c₂
```

Try writing out the (even simpler) induction principle for the unit
type, using ``Bool-ind`` as a model. The result should be a function
from ``⊤`` into the type family `A`, and the argument should be the
data necessary to define that function.

```
-- Exercise:
⊤-ind : {ℓ : Level}
     → {C : ⊤ → Type ℓ}
     → C tt
     → ((x : ⊤) → C x)

⊤-ind c tt = c
```

The recursion principle for `A ⊎ B` is upgraded to an induction
principle in a similar way. Back in ``⊎-rec``, the inputs were maps
`A → C` and `B → C`. If `C` is now a type family dependent on `A ⊎ B`,
these maps have to land in `C x`, where `x` is some element of
`A ⊎ B`. Luckily, there are candidates for what `x` should be in both
cases: take the ``inl`` or ``inr`` of the input `a : A` or `b : B`
respectively.

```
⊎-ind : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''}
  → ((a : A) → C (inl a))
  → ((b : B) → C (inr b))
  → (x : A ⊎ B) → C x
-- Exercise:
⊎-ind l r (inl a) = l a
⊎-ind l r (inr b) = r b
```

``ℕ`` is a little trickier. It is best to remember ordinary
mathematical induction and think of `C` as some property of the
natural numbers that we are trying to prove is true for every natural
number. The first input is the base case of type `C zero`, the claim
that the property `C` holds for ``zero``. Then we have the inductive
step for ``suc`` saying that, for any `n : ℕ`, if `C` holds for `n`
then it also holds for `suc n`.

If we can provide both of those things, then we get a function from
`(n : ℕ) → C n`, meaning that `C` holds for every `n`.

```
ℕ-ind : {ℓ : Level} {C : ℕ → Type ℓ}
  → (z : C zero)
  → (r : (n : ℕ) → C n → C (suc n))
  → ((n : ℕ) → C n)
-- Exercise:
ℕ-ind z r zero = z
ℕ-ind z r (suc n) = r n (ℕ-ind z r n)
```

We don't often need to use ``Bool-ind``, ``⊎-ind`` or ``ℕ-ind``; we
can instead use the pattern matching features of Agda directly.


## Quantifiers

One thing we are still missing from ordinary logic is
*quantification*, that is, the propositions

* "for all elements `x : A`, the proposition `P x` holds", a.k.a. `∀ x. P(x)`, and
* "there exists an element `x : A` so that `P x`" holds, a.k.a. `∃ x. P(x)`.

For our purposes here, we will consider any type family `P : A → Type`
as expressing a predicate on elements of `A`. For example, we have the
predicate on natural numbers that identifies when the natural number
is ``zero``.

```
isZeroP : ℕ → Type
isZeroP zero = ⊤
isZeroP (suc n) = ∅
```

In cases like this where we already have a map into ``Bool``, we
can turn it into a predicate by applying ``IsTrue``.

```
isEvenP : ℕ → Type
isEvenP n = IsTrue (isEven n)

isOddP : ℕ → Type
isOddP n = IsTrue (isOdd n)
```

We can combine these predicates using the operations we've already
seen, for example, we can form the predicate on natural numbers `n`
that the number `n` is even or odd.

```
evenOrOdd : (n : ℕ) → Type
evenOrOdd n = isEvenP n ⊎ isOddP n
```

Of course this should be true for *every* element `n`. The proposition
`∀ n. P(n)` is represented by a dependent function from natural
numbers `n` to proofs that `evenOrOdd n` holds.

```
∀-evenOrOdd : (n : ℕ) → evenOrOdd n
-- Exercise:
∀-evenOrOdd zero = inl tt
∀-evenOrOdd (suc n) with ∀-evenOrOdd n
... | inl ev = inr ev
... | inr od = inl od
```

Try another simple case:

```
∀-zeroImpliesEven : (n : ℕ) → (isZeroP n) → (isEvenP n)
-- Exercise:
∀-zeroImpliesEven zero = λ x → x
∀-zeroImpliesEven (suc n) = ∅-rec
```

For the proposition `∃ n. P(n)`, the obvious thing to try is a
dependent pair: that is, a proof of `∃ n. P(n)` should be an actual
example of an `n` together with a proof that `P(n)` holds. So, we
might represent the proposition that there exists an even number as:

```
Even : Σ[ n ∈ ℕ ] isEvenP n
Even = 2 , tt
```

This interpretation of `∃` is not quite right for similar reasons that
``⊎`` is not quite right. After all, there are lots of different even
numbers that we can use to inhabit the above type, and so the type
represents more information than the mere proposition that there
exists an even number: it comes with a specific choice of one. Again
we will fix this in Lecture 2-7.

For the following exercises, you should recall that ``¬`` is simply
functions into ``∅``. Once you unfold that definition, the below
exercises are *exactly* two functions that we have seen before.

```
¬Σ→forall¬ : {A : Type} {B : A → Type}
  → ¬ (Σ[ a ∈ A ] B a) → (a : A) → ¬ B a
-- Exercise:
¬Σ→forall¬ = λ f a b → f (a , b)

forall¬→¬Σ : {A : Type} {B : A → Type}
  → ((a : A) → ¬ B a) → ¬ (Σ[ a ∈ A ] B a)
-- Exercise:
forall¬→¬Σ = λ f (a , b) → f a b
```


## Decidable Types

There is another crucial way in which constructive logic differs from
classical logic: the Law of Excluded Middle. For propositions
represented as Booleans, we saw in ``≡Bool-LEM`` that every Boolean
element is either ``true`` or ``false``. It seems reasonable for
something similar to be true for propositions as types.

And yet, you will have a hard time proving the following!

```
-- Uncomment to try if you want!
-- impossible-LEM : {ℓ : Level} (P : Type ℓ) → (¬ P) ⊎ P
-- impossible-LEM = {!!}
```

and in fact, the two impossible problems we have seen so far are
related: as soon as you can solve one, you can solve the other.

```
-- If you have `LEM` for a type `P`, then you have ¬¬-implies
LEM→¬¬implies : {ℓ : Level} {P : Type ℓ}
  → ((¬ P) ⊎ P)
  → (¬ ¬ P → P)
-- Exercise:
LEM→¬¬implies (inl np) = λ nnp → ∅-rec (nnp np)
LEM→¬¬implies (inr p) = λ _ → p

-- We almost have LEM for any particular `P`:
¬¬LEM : {ℓ : Level} {P : Type ℓ} → ¬ ¬ ((¬ P) ⊎ P)
-- Exercise:
¬¬LEM x = x (inl (λ p → x (inr p)))

-- Suppose you have `¬¬implies` for `(¬ P) ⊎ P`, then:
¬¬implies→LEM : {ℓ : Level} {P : Type ℓ}
              → (¬ ¬ ((¬ P) ⊎ P) → (¬ P) ⊎ P)
              → ((¬ P) ⊎ P)
-- Exercise:
¬¬implies→LEM f = f (λ x → x (inl (λ p → x (inr p))))
```

So if we have a general proposition `P`, we cannot split into cases
for whether `P` holds or not this: would be saying that we always have
an element of `P ⊎ ¬ P` telling us whether a proposition is true.
Remember, in constructive logic, we can't assume that every
proposition is either true or false.

For some specific types however, we *can* show that `P ⊎ ¬ P` holds:
we call such types "decidable". So, a proposition `P` is decidable if
we can prove that either `P` or `¬ P`.

The following type is essentially identical to the type `P ⊎ ¬ P`, but
we define a new type so we can give it more meaningful constructor
names.

```
data Dec {ℓ : Level} (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
```

Here are the simplest examples:

```
Dec⊤ : Dec ⊤
-- Exercise:
Dec⊤ = yes tt

Dec∅ : Dec ∅
-- Exercise:
Dec∅ = no ∅-rec
```

The predicates we defined on data types so far are all decidable
because we built them out of ``⊤`` and ``∅``.

```
Dec-isEvenP : (n : ℕ) → Dec (isEvenP n)
-- Exercise:
Dec-isEvenP zero = Dec⊤
Dec-isEvenP (suc zero) = Dec∅
Dec-isEvenP (suc (suc n)) = Dec-isEvenP n
```

In particular, observational equality of ``Bool`` and ``ℕ`` is
decidable. Just pattern match and observe whether or not they are
equal!

```
Dec-≡Bool : (a b : Bool) → Dec (a ≡Bool b)
-- Exercise:
Dec-≡Bool true true = Dec⊤
Dec-≡Bool true false = Dec∅
Dec-≡Bool false true = Dec∅
Dec-≡Bool false false = Dec⊤

Dec-≡ℕ : (a b : ℕ) → Dec (a ≡ℕ b)
-- Exercise:
Dec-≡ℕ zero zero = Dec⊤
Dec-≡ℕ zero (suc b) = Dec∅
Dec-≡ℕ (suc a) zero = Dec∅
Dec-≡ℕ (suc a) (suc b) = Dec-≡ℕ a b
```

We further discuss constructive mathematics and its limits in Lecture
3-3.


## References and Further Reading

* The original *[Homotopy Type Theory]* book:
  * Propositions as Types: Chapters 1.11 and 3.2
* Egbert Rijke's *[Introduction to Homotopy Type Theory]*:
  * Obsercational Equality: Chapter 6.3
  * Propositions as Types: Chapter 7.1
  * Decidable Types: Chapter 8.1
* Martin Escardo's [Lecture Notes]:
  * [Negation]

[Homotopy Type Theory]: https://homotopytypetheory.org/book/
[Introduction to Homotopy Type Theory]: https://arxiv.org/abs/2212.11082
[Lecture Notes]: https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/index.htmlure-Notes/HoTT-UF-Agda.html
[Negation]: https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#negation
