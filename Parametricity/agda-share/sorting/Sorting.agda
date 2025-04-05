module Sorting where

open import Logic
open import Natural
open import Vector

infix 20 _,_
data Σ (a : Set)(P : a -> Prop) : Set where
  _,_ : (x : a) (pf : P x) -> Σ a P


Sorted : {n : Nat} -> Vec Nat n -> Prop
Sorted []             = ⊤
Sorted (x :: [])      = ⊤
Sorted (x :: y :: zs) = x <= y ∧ Sorted (y :: zs)

dec-Sorted : {n : Nat} -> Decidable (Sorted {n})
dec-Sorted []        = pfl True
dec-Sorted (x :: []) = pfl True
dec-Sorted (x :: y :: zs) with dec-<= x y | dec-Sorted (y :: zs)
...                       | pfl x<=y  | pfl srt  = pfl (x<=y ^ srt)
...                       | pfr ¬x<=y | _        = pfr (\p -> contradict-l ¬x<=y p)
...                       | _         | pfr ¬srt = pfr (\q -> contradict-r ¬srt q)

insert : {n : Nat} -> Nat -> Vec Nat n -> Vec Nat (succ n)
insert k [] = k :: []
insert k (x :: xs) with dec-<= k x
...                | pfl _ = k :: x :: xs
...                | pfr _ = x :: insert k xs

insert-lemma₀ :  {n : Nat}
                 (x : Nat)
                 (v : Vec Nat n)
              -> Sorted (x :: v)
              -> All (_<=_ x) v
insert-lemma₀ x []        srt = True 
insert-lemma₀ x (y :: ys) (x<=y ^ srt-ys) = x<=y ^ 
     All-trans ys (∀trans-<= x<=y) (insert-lemma₀ y ys srt-ys) 

insert-lemma₁ :  {n : Nat}
                 (x k : Nat)
                 (v : Vec Nat n) 
              -> Sorted (x :: v)
              -> x <= k
              -> All (_<=_ x) (insert k v)
insert-lemma₁ x k []        srt x<=k = x<=k ^ True  
insert-lemma₁ x k (y :: ys) (x<=y ^ srt-ys) x<=k with dec-<= k y
...           | pfl k<=y  = x<=k ^ (x<=y ^ All-trans ys 
                                                     (∀trans-<= x<=y)
                                                     (insert-lemma₀ y ys srt-ys)) 
...           | pfr ¬k<=y = x<=y ^ All-trans (insert k ys)
                                             (∀trans-<= x<=y)
                                             (insert-lemma₁ y k ys srt-ys (¬<=->= ¬k<=y))  

insert-lemma₂ :  {n : Nat}
                 (x k e : Nat)
                 (v es : Vec Nat n)
              -> All (_<=_ x) (insert k v)
              -> insert k v ≡ e :: es
              -> x <= e
insert-lemma₂ x .e e [] [] (x<=e ^ _) ≡-refl = x<=e
insert-lemma₂ x k e (y :: ys) es Apf eq with dec-<= k y
insert-lemma₂ x .e e (y :: ys) .(y :: ys) (x<=e ^ _) ≡-refl | pfl e<=y = x<=e 
insert-lemma₂ x k e (.e :: ys) .(insert k ys) (x<=e ^ _) ≡-refl | pfr ¬k<=y = x<=e

refl-vec : {a : Set} {n : Nat} (v : Vec a n) -> v ≡ v
refl-vec v = ≡-refl

data Inspect' {a : Set} (P : a -> Prop) (x : a) : Set where
  it' : (y : a) -> x ≡ y -> (pf : P y) -> Inspect' P x

inspect' : {a : Set} {P : a -> Prop} (x : a) (pf : P x) -> Inspect' P x
inspect' x pf = it' x ≡-refl pf

insert-Sorted : {n k : Nat} {v : Vec Nat n} -> (srt : Sorted v) -> Sorted (insert k v)
insert-Sorted {zero}          {k} {[]}           srt = True 
insert-Sorted {succ zero}     {k} {x :: []}      srt with dec-<= k x
insert-Sorted {succ zero} {_} {x :: []} srt | pfl pf = pf ^ True  
insert-Sorted {succ zero} {_} {x :: []} srt | pfr pf = ¬<=->= pf ^ True  
insert-Sorted {succ (succ n)} {k} {x :: y :: zs} (x<=y ^ srt-yzs) with dec-<= k x
...                | pfl k<=x  = k<=x ^ (x<=y ^ srt-yzs) 
...                | pfr ¬k<=x with inspect' {_} {Sorted} (insert k (y :: zs))
                                       (insert-Sorted {succ n} {k} {y :: zs} srt-yzs)
...                      | it' (e :: e' :: es) es≡ins (e<=e' ^ srt-es)
   = let A<=x = insert-lemma₁ x k (y :: zs) (x<=y ^ srt-yzs) (¬<=->= ¬k<=x)
     in ≡-resp (\l -> Sorted (x :: l)) (≡-symm es≡ins)
          (insert-lemma₂ x k e (y :: zs) (e' :: es) A<=x es≡ins ^ (e<=e' ^ srt-es))


sort : {n : Nat} -> Vec Nat n -> Vec Nat n
sort []        = []
sort (x :: xs) = insert x (sort xs)

sort-Sorted : {n : Nat} -> (v : Vec Nat n) -> Sorted (sort v)
sort-Sorted []        = _
sort-Sorted (x :: xs) = insert-Sorted {_} {_} {sort xs} (sort-Sorted xs)

-- Easy version of the proof
data _∼_ {a : Set} : {n : Nat} (v v' : Vec a n) -> Set where
  ∼-id : {n : Nat} (v : Vec a n) -> v ∼ v
  ∼-:: : {n : Nat} (x : a)
                   (v v' : Vec a n)
                   (pf : v ∼ v')
       -> (x :: v) ∼ (x :: v')
  ∼-sw : {n : Nat} (x y : a)
                   (v v' : Vec a n)
                   (pf : v ∼ v')
       -> (x :: y :: v) ∼ (y :: x :: v')
  -- cheat a bit
  ∼-tr : {n : Nat}
         (v v' v'' : Vec a n)
         (pf  : v ∼ v')
         (pf' : v' ∼ v'')
       -> v ∼ v''

∼-symm : {a : Set} {n : Nat} (xs ys : Vec a n) -> xs ∼ ys -> ys ∼ xs
∼-symm .ys             ys             (∼-id .ys)         = ∼-id ys
∼-symm .(x :: v) .     (x :: v')      (∼-:: x v v' pf)   = ∼-:: x v' v (∼-symm v v' pf)
∼-symm .(x :: y :: v) .(y :: x :: v') (∼-sw x y v v' pf) = ∼-sw y x v' v (∼-symm v v' pf)
∼-symm .xs            .zs             (∼-tr xs ys zs xy yz)
  = ∼-tr zs ys xs (∼-symm ys zs yz) (∼-symm xs ys xy)

∼-lemma : {a : Set} {n : Nat} (k x : a) (xs : Vec a n) (v : Vec a (succ n))
          -> (k :: xs) ∼ v -> (k :: x :: xs) ∼ (x :: v)
∼-lemma k x xs v pf = ∼-tr (k :: x :: xs) (x :: k :: xs) (x :: v)
                           (∼-sw k x xs xs (∼-id xs)) (∼-:: x (k :: xs) v pf)


∼-insert : {n : Nat} (k : Nat) (xs : Vec Nat n) -> (k :: xs) ∼ insert k xs
∼-insert k []        = ∼-id (k :: [])
∼-insert k (x :: xs) with dec-<= k x
...                  | pfl k<=x = ∼-id (k :: x :: xs)
...                  | pfr k>x  = ∼-lemma k x xs (insert k xs) (∼-insert k xs)

∼-sort : {n : Nat} (v : Vec Nat n) -> v ∼ sort v
∼-sort []        = ∼-id []
∼-sort (x :: xs) = ∼-tr (x :: xs) (x :: sort xs) (insert x (sort xs))
                     (∼-:: x xs (sort xs) (∼-sort xs))
                     (∼-insert x (sort xs))

test = 5 :: 1 :: 3 :: 0 :: 10 :: 12 :: []






{-

This version is commented out, because I'm unable to find a notion of
permutation that is both minimal, and doesn't result in my bumping up
against walls. Technically, the above version should be sufficient,
since the proof is inductive, and taking transitivity as an axiom shouldn't
change what proofs are available.

data _∈_ {a : Set} (x : a) : {n : Nat} -> Vec a n -> Set where
  now   : {n : Nat} (xs : Vec a n) -> x ∈ (x :: xs)
  later : {n : Nat} (y : a) (ys : Vec a n)
          (pf : x ∈ ys)
        -> x ∈ (y :: ys)

remove : {a : Set} {n : Nat} {x : a} {ys : Vec a (succ n)} -> x ∈ ys -> Vec a n
remove (now xs) = xs
remove (later y [] ())
remove (later y (_ :: _) pf) = y :: remove pf

data _≃_ {a : Set} : {n : Nat} -> (xs ys : Vec a n) -> Set where
  ≃-[] : [] ≃ []
  ≃-:: : {n : Nat} 
         (x : a) (xs : Vec a n) (ys : Vec a (succ n))
         (e : x ∈ ys)
       -> xs ≃ remove e
       -> x :: xs ≃ ys

∈-insert : {n : Nat} (x : Nat) (xs : Vec Nat n) -> x ∈ insert x xs
∈-insert x []        = now []
∈-insert x (y :: ys) with dec-<= x y
...                  | pfl x<=y = now (y :: ys)
...                  | pfr x>y  = later y (insert x ys) (∈-insert x ys)

≃-refl : {a : Set} {n : Nat} (xs : Vec a n) -> xs ≃ xs
≃-refl [] = ≃-[]
≃-refl (x :: xs) = ≃-:: x xs (x :: xs) (now xs) (≃-refl xs)

{-
≃-symm : {a : Set} {n : Nat} {xs ys : Vec a n} -> xs ≃ ys -> ys ≃ xs
≃-symm ≃-[] = ≃-[]
≃-symm {a} {succ n} {.(y :: xs)} {y :: ys}
  (≃-:: .y xs .(y :: ys) (now .ys) xs≃ys)
  = ≃-:: y ys (y :: xs) (now xs) (≃-symm xs≃ys)
≃-symm {a} {succ n} {.(x :: xs)} {y :: ys}
  (≃-:: x xs .(y :: ys) (later .y .ys x∈ys) xs≃r)
  = {!!}
-}
∈-promote : {a : Set} {n : Nat} (x y : a) (zs : Vec a (succ n))
            (e : y ∈ zs) -> x ∈ remove e -> x ∈ zs
∈-promote x y (z :: [])        y∈zs                      ()
∈-promote x .z (z :: z' :: zs) (now .(z' :: zs))         x∈rem = later z (z' :: zs) x∈rem
∈-promote .z y (z :: z' :: zs) (later .z .(z' :: zs) pf) (now .(remove pf)) = now (z' :: zs)
∈-promote x y (z :: z' :: zs) (later .z .(z' :: zs) y∈z'zs)
  (later .z .(remove y∈z'zs) x∈rem)
  = later z (z' :: zs) (∈-promote x y (z' :: zs) y∈z'zs x∈rem) 

∈-≃ : {a : Set} {n : Nat} (x : a) (ys zs : Vec a n) -> x ∈ ys -> ys ≃ zs -> x ∈ zs
∈-≃ _ [] [] () _
∈-≃ .y (y :: ys) (z :: zs) (now .ys) (≃-:: .y .ys .(z :: zs) y∈zs _) = y∈zs
∈-≃  x (y :: ys) (z :: zs) (later .y .ys x∈ys) (≃-:: .y .ys .(z :: zs) y∈zzs ys≃rem)
  = ∈-promote x y (z :: zs) y∈zzs x∈rem
 where
 x∈rem : x ∈ remove y∈zzs
 x∈rem = ∈-≃ x ys (remove y∈zzs) x∈ys ys≃rem

{-
≃-::remove : {a : Set} {n : Nat} (x : a) (xs : Vec a (succ n))
             (e : x ∈ xs) -> xs ≃ x :: remove e
≃-::remove x .(x :: xs) (now xs)        = ≃-refl _
≃-::remove x .(y :: []) (later y [] ())
≃-::remove x .(y :: y' :: ys) (later y (y' :: ys) x∈y'ys) = {!!}
 where
 y'ys≃xyr : y' :: ys ≃ x :: remove x∈y'ys
 y'ys≃xyr = ≃-::remove x (y' :: ys) x∈y'ys




≃-un:: : {a : Set} {n : Nat} {x : a} {ys zs : Vec a n}
       -> x :: ys ≃ x :: zs -> ys ≃ zs
≃-un:: {a} {n} {x} {ys} {zs} (≃-:: .x .ys .(x :: zs) (now .zs) ys≃zs) = ys≃zs
≃-un:: {a} {n} {x} {ys} {zs}
  (≃-:: .x .ys .(x :: zs) (later .x .zs pf) ys≃rem)
  = {!!}

≃-remove : {a : Set} {n : Nat} {x : a} {ys zs : Vec a (succ n)}
           (x∈ys : x ∈ ys) -> (x∈zs : x ∈ zs) -> ys ≃ zs
         -> remove x∈ys ≃ remove x∈zs
≃-remove (now ys) (now zs)        ys≃zs = {!!}
≃-remove (now xs) (later y ys pf) ys≃zs = {!!}
≃-remove (later y ys pf) x∈zs ys≃zs = {!!}


≃-trans : {a : Set} {n : Nat} (xs ys zs : Vec a n) -> xs ≃ ys -> ys ≃ zs -> xs ≃ zs
≃-trans [] [] [] ≃-[] ≃-[] = ≃-[]
≃-trans (x :: xs) (.x :: ys) (.x :: zs)
        (≃-:: .x .xs .(x :: ys) (now .ys) xs≃ys)
        (≃-:: .x .ys .(x :: zs) (now .zs) ys≃zs)
    = ≃-:: x xs (x :: zs) (now zs) (≃-trans xs ys zs xs≃ys ys≃zs)

≃-trans (x :: xs) (.x :: ys) (z :: zs)
        (≃-:: .x .xs .(x :: ys) (now .ys) xs≃ys)
        (≃-:: .x .ys .(z :: zs) (later .z .zs x∈zs) ys≃rem)
    = ≃-:: x xs (z :: zs) (later z zs x∈zs) (≃-trans xs ys _ xs≃ys ys≃rem)

≃-trans (x :: xs) (y :: ys) (.y :: zs)
        (≃-:: .x .xs .(y :: ys) (later .y .ys x∈ys) xs≃rem) -- xs ≃ remove (later y ys x∈ys)
        (≃-:: .y .ys .(y :: zs) (now .zs) ys≃zs)
    = ≃-:: x xs (y :: zs) (later y zs x∈zs) {!!}
  where
  x∈zs : x ∈ zs
  x∈zs = ∈-≃ x ys zs x∈ys ys≃zs

≃-trans (x :: xs) (y :: ys) (z :: zs)
        (≃-:: .x .xs .(y :: ys) (later .y .ys x∈ys) xs≃rem)
        (≃-:: .y .ys .(z :: zs) (later .z .zs y∈zs) ys≃rem) = {!!}
-}

≃-insert : {n : Nat} (x : Nat) (xs : Vec Nat n) -> x :: xs ≃ insert x xs
≃-insert x []         = ≃-:: x [] (x :: []) (now []) ≃-[]
≃-insert x (y :: ys) with dec-<= x y
...                  | pfl x<=y = ≃-refl (x :: y :: ys)
...                  | pfr x>y  = {!!}
-}
