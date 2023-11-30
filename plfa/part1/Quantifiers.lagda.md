---
title     : "Quantifiers: Universals and existentials"
permalink : /Quantifiers/
---

```agda
module plfa.part1.Quantifiers where
```

This chapter introduces universal and existential quantification.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; subst)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_⇔_; _≃_; extensionality; ∀-extensionality)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
```


## Universals

We formalise universal quantification using the dependent function
type, which has appeared throughout this book.  For instance, in
Chapter Induction we showed addition is associative:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

which asserts for all natural numbers `m`, `n`, and `p`
that `(m + n) + p ≡ m + (n + p)` holds.  It is a dependent
function, which given values for `m`, `n`, and `p` returns
evidence for the corresponding equation.

In general, given a variable `x` of type `A` and a proposition `B x`
which contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type `A`
the proposition `B M` holds.  Here `B M` stands for the proposition
`B x` with each free occurrence of `x` replaced by `M`.  Variable `x`
appears free in `B x` but bound in `∀ (x : A) → B x`.

Evidence that `∀ (x : A) → B x` holds is of the form

    λ (x : A) → N x

where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L M`
provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.

Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
```agda
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M
```
As with `→-elim`, the rule corresponds to function application.

Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.

Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
```agda
{-
postulate
  ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
-}
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to      = λ f → ⟨ (λ x → proj₁ (f x)) , (λ x → proj₂ (f x)) ⟩
    ; from    = λ (⟨ f , g ⟩) a → ⟨ f a , g a ⟩
    ; from∘to = λ f → refl
    ; to∘from = λ (⟨ f , g ⟩) → refl
    }

```
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives](/Connectives/).

Hint: you will need to use [`∀-extensionality`](/Isomorphism/#extensionality).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
```agda
{-
postulate
  ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
-}
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) = inj₁ ∘ f
⊎∀-implies-∀⊎ (inj₂ g) = inj₂ ∘ g
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
```agda
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× =
  record
    { to      = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
    ; from    = λ{ ⟨ a , ⟨ b , c ⟩ ⟩ aa → a ; ⟨ a , ⟨ b , c ⟩ ⟩ bb → b ; ⟨ a , ⟨ b , c ⟩ ⟩ cc → c }
    ; from∘to = λ _ → ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl }
    ; to∘from = λ _ → refl
    }
```
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.

Hint: you will need to use [`∀-extensionality`](/Isomorphism/#extensionality).


## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

We formalise existential quantification by declaring a suitable
inductive type:
```agda
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
```
We define a convenient syntax for existentials as follows:
```agda
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx
```
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
```agda
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′
```
Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B M`.

Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
```agda
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
```agda
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y
```
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
```agda
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication](/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
```agda
{-
postulate
  ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
-}
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to      = λ{ ⟨ a , inj₁ ba ⟩ → inj₁ ⟨ a , ba ⟩ ; ⟨ a , inj₂ ca ⟩ → inj₂ ⟨ a , ca ⟩ }
    ; from    = λ{ (inj₁ ⟨ a , ba ⟩) → ⟨ a , inj₁ ba ⟩ ; (inj₂ ⟨ a , ca ⟩) → ⟨ a , inj₂ ca ⟩ }
    ; from∘to = λ{ ⟨ a , inj₁ ba ⟩ → refl ; ⟨ a , inj₂ ca ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ a , ba ⟩) → refl ; (inj₂ ⟨ a , ca ⟩) → refl }
    }
```

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
```agda
{-
postulate
  ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
-}
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ ba , ca ⟩ ⟩ = ⟨ ⟨ a , ba ⟩ , ⟨ a , ca ⟩ ⟩
```
Does the converse hold? If so, prove; if not, explain why.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.

```agda
∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ = 
  record 
    { to      = λ{ ⟨ aa , bt ⟩ → inj₁ bt ; ⟨ bb , bt ⟩ → inj₂ (inj₁ bt) ; ⟨ cc , bt ⟩ → inj₂ (inj₂ bt) }
    ; from    = λ{ (inj₁ baa) → ⟨ aa , baa ⟩ ; (inj₂ (inj₁ bbb)) → ⟨ bb , bbb ⟩ ; (inj₂ (inj₂ bcc)) → ⟨ cc , bcc ⟩ }
    ; from∘to = λ{ ⟨ aa , baa ⟩ → refl ; ⟨ bb , bbb ⟩ → refl ; ⟨ cc , bcc ⟩ → refl }
    ; to∘from = λ{ (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
    }
```

## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations](/Relations/):
```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:

`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction:
```agda
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
```
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:

* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction:
```agda
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)
```
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:

- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

```agda
∃-even' : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd'  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

∃-even' ⟨ zero , 0≡n ⟩ rewrite (sym 0≡n) = even-zero
∃-even' ⟨ suc x , ≡n ⟩ rewrite +-comm x zero
                             | +-suc x x
                             | sym ≡n
                             = even-suc (odd-suc (∃-even' ⟨ x , helper ⟩))
                             where
                             helper : x + (x + zero) ≡ x + x
                             helper rewrite +-comm x zero = refl

∃-odd' ⟨ zero , 1≡n ⟩ rewrite sym 1≡n = odd-suc even-zero
∃-odd' ⟨ suc x , ≡n ⟩ rewrite +-comm x zero
                            | +-suc x x 
                            | +-assoc x x 1
                            | +-comm x 1
                            | +-suc x x
                            | sym ≡n 
                            = odd-suc (∃-even' ⟨ (suc x) , helper ⟩)
                            where
                            helper : suc (x + suc (x + zero)) ≡ suc (suc (x + x))
                            helper rewrite +-comm x zero | +-suc x x = refl

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

∃-even′ ⟨ zero , 0≡n ⟩ rewrite (sym 0≡n) = even-zero
∃-even′ ⟨ suc x , ≡n ⟩ rewrite sym ≡n = even-suc (∃-odd′ ⟨ x , helper ⟩)
  where
  helper : x + (x + zero) + 1 ≡ x + suc (x + 0)
  helper rewrite +-identityʳ x | +-comm (x + x) 1 | +-suc x x = refl

∃-odd′ ⟨ zero , 1≡n ⟩ rewrite sym 1≡n = odd-suc even-zero
∃-odd′ ⟨ suc x , ≡n ⟩ rewrite sym ≡n = odd-suc (∃-even′ ⟨ (suc x) , helper ⟩)
  where
  helper : suc (x + suc (x + zero)) ≡ x + suc (x + 0) + 1
  helper rewrite +-identityʳ x | +-comm x (suc x) | +-comm (x + x) 1 = refl
```

#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

```agda
open import plfa.part1.Relations using (_≤_; z≤n; s≤s; ≤-refl; inv-s≤s)

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

m∸n+n≡m : ∀ {m n : ℕ} → n ≤ m → m ∸ n + n ≡ m
m∸n+n≡m {m} {zero} n≤m = +-identityʳ m
m∸n+n≡m {suc m} {suc n} n≤m rewrite +-suc (m ∸ n) n | m∸n+n≡m (inv-s≤s n≤m) = refl

y≤x+y : ∀ {x y : ℕ} → y ≤ x + y
y≤x+y {zero} {y} = ≤-refl
y≤x+y {suc x} {zero} = z≤n
y≤x+y {suc x} {suc y} rewrite +-suc x y = s≤s y≤x+y

∃-+-≤ : ∀ {x y z : ℕ} → y ≤ z ⇔ ∃[ x ] (x + y ≡ z)
∃-+-≤ {x} {y} {z} =
  record
    { to   = λ y≤z → ⟨ z ∸ y , m∸n+n≡m y≤z ⟩
    ; from = λ{ ⟨ x , refl ⟩ → y≤x+y }
    }
```


## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
```agda
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
```
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
```agda
{-
postulate
  ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
    → ∃[ x ] (¬ B x)
      --------------
    → ¬ (∀ x → B x)
-}
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , ¬Ba ⟩ = λ f → ¬Ba (f a)
```
Does the converse hold? If so, prove; if not, explain why.


#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin](/Naturals/#Bin),
[Bin-laws](/Induction/#Bin-laws), and
[Bin-predicates](/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ] Can b`.

We recommend proving the following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′

    ≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {c c′ : ∃[ b ] Can b} → proj₁ c ≡ proj₁ c′ → c ≡ c′

```agda
open import plfa.part1.Relations using (Bin; ⟨⟩; _O; _I; to; from; One; one; tailO; tailI; Can;
           can-to; zero; can; to∘from≡id; from∘to≡id)

≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One one one = refl
≡One (tailO o) (tailO o′) = cong tailO (≡One o o′)
≡One (tailI o) (tailI o′) = cong tailI (≡One o o′)

¬OneO : ¬ One (⟨⟩ O)
¬OneO = λ{ (tailO ()) }

≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′
≡Can zero zero = refl
≡Can (can x) zero = ⊥-elim (¬OneO x)
≡Can zero (can x) = ⊥-elim (¬OneO x)
≡Can (can o) (can o′) = cong can (≡One o o′)

pr₁ : ∀ {A : Set} {B : A → Set} →  (∃[ x ] B x) → A
pr₁ ⟨ x , _ ⟩ = x

pr₂ : ∀ {A : Set} {B : A → Set} →  (∃xBx : ∃[ x ] B x) → B (pr₁ ∃xBx)
pr₂ ⟨ _ , y ⟩ = y

pr₁≡→pr₂≡ : {c c′ : ∃[ b ] Can b} → (p : pr₁ c ≡ pr₁ c′) → subst Can p (pr₂ c) ≡ pr₂ c′
pr₁≡→pr₂≡ {⟨ b₁ , c₁ ⟩} {⟨ b₂ , c₂ ⟩} p = ≡Can (subst Can p c₁) c₂

pr₁≡×pr₂≡→Can≡ : {c c′ : ∃[ b ] Can b} → (p : pr₁ c ≡ pr₁ c′) → subst Can p (pr₂ c) ≡ pr₂ c′ → c ≡ c′
pr₁≡×pr₂≡→Can≡ {⟨ b₁ , c₁ ⟩} {⟨ b₂ , c₂ ⟩} refl refl = refl

proj₁≡→Can≡ : {c c′ : ∃[ b ] Can b} → pr₁ c ≡ pr₁ c′ → c ≡ c′
proj₁≡→Can≡ {⟨ b₁ , c₁ ⟩} {⟨ b₂ , c₂ ⟩} p = pr₁≡×pr₂≡→Can≡ {⟨ b₁ , c₁ ⟩} {⟨ b₂ , c₂ ⟩} p (pr₁≡→pr₂≡ {⟨ b₁ , c₁ ⟩} {⟨ b₂ , c₂ ⟩} p)

to-bincan : ℕ → ∃[ b ] Can b
to-bincan n = ⟨ to n , can-to n ⟩

ℕ≃Can : ℕ ≃ ∃[ b ] Can b
ℕ≃Can =
  record
    { to      = λ n → ⟨ to n , can-to n ⟩
    ; from    = λ{ ⟨ b , b-can ⟩ → from b }
    ; from∘to = λ n → from∘to≡id n
    ; to∘from = λ{ ⟨ b , can-b ⟩ → proj₁≡→Can≡ (to∘from≡id can-b) }
    }
```


## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
```


## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
