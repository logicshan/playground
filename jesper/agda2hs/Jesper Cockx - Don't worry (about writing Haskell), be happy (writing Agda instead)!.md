Posted by Jesper on October 4, 2022

As we all know, static type systems are great to ensure correctness of our programs. Sadly, in industry many people are forced to work in languages with a weak type system, such as Haskell. What should you do in such a situation? Quit your job? Give up and despair? Perhaps, but I have another suggestion that I’d like to explain in this post: use our tool [`agda2hs`](https://github.com/agda/agda2hs).

What is this `agda2hs`, I hear you asking? Agda2hs is a tool for producing verified and readable Haskell code by extracting it from a (lightly annotated) Agda program. This means you can write your code using Agda’s support for dependent types, interactive editing, and termination checking, and from this `agda2hs` will generate clean and simply typed Haskell code that looks like it was written by hand. Your boss will be amazed that all of your code is correct from the first try, and never even suspect that you secretly proved its correctness in Agda!

## First steps: verifying list insertion

Let’s take a look at an example of how **you** can use `agda2hs` to produce provably correct Haskell code. Suppose we want to insert an element into a sorted list. That’s easy enough:

```
open import Haskell.Prelude

insert : {{Ord a}} → a → List a → List a
insert x [] = x ∷ []
insert x (y ∷ ys) =
  if x < y
  then x ∷ y ∷ ys
  else y ∷ insert x ys

```

The syntax is deliberately chosen to be very close to the corresponding Haskell syntax, except for the swapping of `:` and `::`. I am using some definitions from the [prelude](https://github.com/agda/agda2hs/tree/master/lib/Haskell) that is included with `agda2hs`, in particular the `Ord` type. The double braces `{{}}` indicate an [instance argument](https://agda.readthedocs.io/en/v2.6.2.2/language/instance-arguments.html), which is Agda’s way of doing type classes.

To make `agda2hs` do its magic, there is just one more invocation needed:

```
{-# COMPILE AGDA2HS insert #-}

```

Now, calling `agda2hs` on this file produces the corresponding Haskell code:

```
insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y : ys) = if x < y then x : (y : ys) else y : insert x ys
```

So far, so Haskell. But this looks awfully complicated, how can we ever know it is correct? Prove it, of course! One property that certainly needs to hold is that when we insert an element into a list, then that element should be in the resulting list.

```
data _∈_ (x : a) : List a → Set where
  here  : ∀ {ys}            → x ∈ (x ∷ ys)
  there : ∀ {y ys} → x ∈ ys → x ∈ (y ∷ ys)

insert-elem : ∀ {{_ : Ord a}} (x : a) (xs : List a)
            → x ∈ insert x xs
insert-elem x [] = here
insert-elem x (y ∷ ys) with x < y
... | True  = here
... | False = there (insert-elem x ys)

```

Of course this isn’t enough: defining `insert x _ = x ∷ []` satisfies this specification. Following the ancient tradition, I leave identifying and proving the other properties of insertion as an exercise to the interested reader.

## Intrinsic verification with `agda2hs`

The proof above is an example of _extrinsic_ verification: we first write a simply-typed Haskell-like function and prove properties of it after-the-fact. Another style of proof that is sometimes easier to use is _intrinsic verification_: here we encode the properties directly in the type of our data, so it becomes impossible to write an incorrect function in the first place.

Avoiding the tired example of length-indexed vectors, let’s take a look instead at the type of height-indexed trees, i.e. trees that are indexed by the maximum length of the paths to their leaves. There are two ways to construct a height-indexed tree: `Tip` produces a tree of height `0`, while `Bin` takes an element of type `a` and two subtrees, and produces a tree of height 1 + the _maximum_ of the heights of the two subtrees.

```
maxNat : Nat → Nat → Nat
maxNat zero    n       = n
maxNat (suc m) zero    = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

data Tree (a : Set) : (@0 height : Nat) → Set where
  Tip : Tree a 0
  Bin : ∀ {@0 l r}
      → a → Tree a l → Tree a r → Tree a (suc (maxNat l r))
{-# COMPILE AGDA2HS Tree #-}

```

Since Haskell tends to get confused by terms appearing at the type level, we need some way to indicate to `agda2hs` that we do _not_ want the second argument to `Tree` (the `height : Nat`) to be translated to Haskell. To do this, `agda2hs` makes use of the [erasure annotations](https://agda.readthedocs.io/en/v2.6.2.2/language/runtime-irrelevance.html) `@0` that are built into Agda. The nice thing about these erasure annotations is that Agda will check that you never return or pattern match on an erased argument, so erasing them does not affect the computational behaviour of your program. The output is a simple Haskell implementation of binary trees:

```
data Tree a = Tip
            | Bin a (Tree a) (Tree a)
```

To implement functions on indexed datatypes, it is often needed to _transport_ an element between two types when we know that their indices are provably equal. For this we can define the function `transport` (sometimes also called `subst`):

```
transport : (@0 p : @0 a → Set) {@0 m n : a}
          → @0 m ≡ n → p m → p n
transport p refl t = t
{-# COMPILE AGDA2HS transport #-}

```

That’s surely a lot of erasure annotations! In particular, the type operator `p` both needs to be erased itself, but also needs to accept erased inputs `m` and `n` so we can erase them as well. The result is that `transport` is compiled to a plain identity function:

```
transport :: p -> p
transport t = t
```

Now we can implement the `mirror` function which recursively flips the left and right subtrees at each node.

```
@0 max-comm : (@0 l r : Nat) → maxNat l r ≡ maxNat r l
max-comm zero    zero    = refl
max-comm zero    (suc r) = refl
max-comm (suc l) zero    = refl
max-comm (suc l) (suc r) = cong suc (max-comm l r)

mirror : ∀ {@0 h} → Tree a h → Tree a h
mirror Tip =  Tip
mirror {a = a} (Bin {l} {r} x lt rt)
  = transport (Tree a)
              (cong suc (max-comm r l))
              (Bin x (mirror rt) (mirror lt))
{-# COMPILE AGDA2HS mirror #-}

```

In the recursive branch of the mirror function, we need to convert a tree of type `Tree a (suc (max r l))` to type `Tree a (suc (max l r))`. To do this, we `transport` by the proof of commutativity of `max`. We can now tell that `mirror` preserves the height of the tree _by construction_, simply from its type.

Running `agda2hs` on this function produces the following:

```
mirror :: Tree a -> Tree a
mirror Tip = Tip
mirror (Bin x lt rt) = transport (Bin x (mirror rt) (mirror lt))
```

While this is functional, the function `transport` still appears in the Haskell code! GHC is probably smart enough to inline this definition, but our boss might be able to tell that we’re not writing this code by hand.

To avoid this problem, `agda2hs` allows us to annotate functions as `transparent` if they become an identity function after erasing all `@0` arguments:

```
{-# COMPILE AGDA2HS transport transparent #-}
```

With this change, `agda2hs` produces the code we want, and we are saved from our boss. Phew!

```
mirror :: Tree a -> Tree a
mirror Tip = Tip
mirror (Bin x lt rt) = Bin x (mirror rt) (mirror lt)
```

## Making monads obey the law

At the moment of writing this blog post, `agda2hs` is still in its infancy, so it does not yet support all of Haskell’s main features. One especially glaring omission at the moment is the lack of support for `do`\-notation:

```
headMaybe : List a → Maybe a
headMaybe [] = Nothing
headMaybe (x ∷ xs) = Just x
{-# COMPILE AGDA2HS headMaybe #-}

tailMaybe : List a → Maybe (List a)
tailMaybe [] = Nothing
tailMaybe (x ∷ xs) = Just xs
{-# COMPILE AGDA2HS tailMaybe #-}

third : List a → Maybe a
third xs = do
  ys ← tailMaybe xs
  zs ← tailMaybe ys
  z  ← headMaybe zs
  return z
{-# COMPILE AGDA2HS third #-}

```

While we can use `do` notation in Agda as shown in the example above, this is not preserved in the translation to Haskell:

```
headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x : xs) = Just x

tailMaybe :: [a] -> Maybe [a]
tailMaybe [] = Nothing
tailMaybe (x : xs) = Just xs

third :: [a] -> Maybe a
third xs
  = tailMaybe xs >>=
      \ ys -> tailMaybe ys >>= \ zs -> headMaybe zs >>= return
```

Still, we can already do things that would not be possible in Haskell, e.g. prove the monad laws for each of our monads. To do this, we first declare a typeclass `LawfulMonad` that is parametrized by a `Monad m` instance and has three fields, one for each of the three monad laws:

```
record LawfulMonad (m : Set → Set)
                   {{iMonad : Monad m}} : Set₁ where
  field
    left-id : ∀ {a b} (x : a) (f : a → m b)
            → (return x >>= f) ≡ f x
    right-id : ∀ {a} (k : m a)
             → (k >>= return) ≡ k
    assoc : ∀ {a b c} (k : m a)
          → (f : a → m b) (g : b → m c)
          → ((k >>= f) >>= g) ≡ (k >>= (λ x → f x >>= g))
open LawfulMonad

```

We can then prove the monad laws for a monad by defining an instance of this class, for example for the `Maybe` monad:

```
instance
  _ : LawfulMonad Maybe
  _ = λ where
    .left-id  x        f   → refl
    .right-id Nothing      → refl
    .right-id (Just x)     → refl
    .assoc    Nothing  f g → refl
    .assoc    (Just x) f g → refl

```

Thanks to Agda’s built-in support for eta-equality on function types, proving the monad laws for the reader monad is especially straightforward:

```
instance
  _ : {r : Set} → LawfulMonad (λ a → (r → a))
  _ = λ where
    .left-id   x f   → refl
    .right-id  k     → refl
    .assoc     k f g → refl

```

## Coinduction, sizes, and cubical, oh my!

Working with `agda2hs` can be quite nice since you have the full power of Agda at your disposal for writing proofs. As an example, let’s implement coinductive (infinite) streams, and prove fusion of subsequent maps on streams by using [Cubical Agda](https://agda.readthedocs.io/en/v2.6.2.2/language/cubical.html)! As a warning: this is very much still an experiment, so expect some rough edges. I’ve made a [PR for improving compatibility between `agda2hs` and Cubical Agda](https://github.com/agda/agda2hs/pull/111), which should be merged soon.

First, to define coinductive types in `agda2hs` we need to import the `Thunk` type. This type is ‘transparent’ (i.e. not compiled to Haskell) but it is necessary to make Agda understand that this is really a coinductive structure, and it should do productivity checking rather than termination checking.

```
open import Haskell.Prim.Thunk

```

We can then use the `Thunk` type to mark constructor arguments that should be treated ‘lazily’:

```
data Stream (a : Set) (@0 i : Size) : Set where
  _:>_ : a → Thunk (Stream a) i → Stream a i
{-# COMPILE AGDA2HS Stream #-}

```

We make use of [sized types](https://agda.readthedocs.io/en/v2.6.2.2/language/sized-types.html) to indicate the size of a stream, i.e. the depth to which the stream has been defined. This helps Agda’s productivity checker to determine that the functions for producing streams we will define below are productive. Since the size is marked as erased with `@0`, it does not appear in the Haskell code:

```
data Stream a = (:>) a (Stream a)
```

Defining functions that consume a stream is easy enough:

```
headS : Stream a ∞ → a
headS (x :> _) = x
{-# COMPILE AGDA2HS headS #-}

```

To force evaluation of a thunk, we use the syntax `.force`:

```
tailS : Stream a ∞ → Stream a ∞
tailS (_ :> xs) = xs .force
{-# COMPILE AGDA2HS tailS #-}

```

```
headS :: Stream a -> a
headS (x :> _) = x

tailS :: Stream a -> Stream a
tailS (_ :> xs) = xs
```

To define a function that produces a stream, we need to define the tail “lazily”. In Agda, that is done using the syntax `λ where .force → ...`.

```
repeat : a → Stream a i
repeat x = x :> λ where .force → repeat x
{-# COMPILE AGDA2HS repeat #-}

```

The function is compiled as expected, and any trace of `Thunk` and `force` is gone:

```
repeat :: a -> Stream a
repeat x = x :> repeat x
```

Similarly, we define a `map` function on streams:

```
mapS  : (a → b) → Stream a i → Stream b i
mapS  f (x :> xs) =
  (f x) :> λ where .force → mapS f (xs .force)
{-# COMPILE AGDA2HS mapS #-}

```

```
mapS :: (a -> b) -> Stream a -> Stream b
mapS f (x :> xs) = f x :> mapS f xs
```

As an example, we can use this to implement the infinite stream of natural numbers:

```
nats : Stream Int i
nats = 0 :> λ where .force → mapS (λ x → 1 + x) nats
{-# COMPILE AGDA2HS nats #-}

```

Finally, let me make good on my promise and prove map fusion on streams by using Cubical Agda. Step one: import the `PathP` type and define the cubical equality type `_=P_` in terms of it:

```
open import Agda.Primitive.Cubical using (PathP)

_=P_ : {a : Set ℓ} → (x y : a) → Set ℓ
_=P_ {a = a} = PathP (λ _ → a)

```

Step two: ~[draw the owl](https://knowyourmeme.com/memes/how-to-draw-an-owl)~ prove the fusion:

```
mapS-fusion  : (f : a → b) (g : b → c) (s : Stream a i)
             →  mapS {i = i} g (mapS {i = i} f s)
             =P mapS {i = i} (λ x → g (f x)) s
mapS-fusion  f g (hd :> tl) i =
  (g (f hd)) :> λ where .force → mapS-fusion f g (tl .force) i

```

If you haven’t seen Cubical Agda being used for proving bisimilarity before, this probably looks like magic. But if it is magic, it is magic provided by Cubical Agda, not by `agda2hs`. The _real_ magic is the fact that `agda2hs` does not even need to know anything about Cubical Agda for this proof to work!

If you want to try out `agda2hs` for yourself, you can get it from [Github](https://github.com/agda/agda2hs). If you are keen to see more examples and learn of the design and implementation of `agda2hs`, you can take a look at our recent [paper at the Haskell Symposium](https://dl.acm.org/doi/pdf/10.1145/3546189.3549920). And if you have any comments or suggestions about this post, you can always send them to me on [Mastodon](https://types.pl/agdakx) or via [email](mailto:jesper@sikanda.be).