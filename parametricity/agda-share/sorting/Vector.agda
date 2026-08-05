
module Vector where

open import Logic
open import Natural

infixr 45 _::_
data Vec (a : Set) : Nat -> Set where
  []   : Vec a zero
  _::_ : forall {n} -> (x : a) -> (xs : Vec a n) -> Vec a (succ n)


All : {a : Set} {n : Nat} (P : a -> Prop) -> Vec a n -> Prop
All P []        = ⊤
All P (x :: xs) = P x ∧ All P xs

All-trans : {n : Nat}
            {a : Set}
            {P : a -> Prop}
            {Q : a -> Prop}
            (v : Vec a n)
          -> (forall x -> P x -> Q x)
          -> All P v
          -> All Q v
All-trans [] P→Q AP = True 
All-trans (x :: xs) P→Q (Px ^ APxs) = P→Q x Px ^ All-trans xs P→Q APxs  

≡-cons : {a : Set} {x y : a} {n : Nat} {xs ys : Vec a n} -> x ≡ y -> xs ≡ ys -> x :: xs ≡ y :: ys
≡-cons ≡-refl ≡-refl = ≡-refl

≡-head : {a : Set} {x y : a} {n : Nat} {xs ys : Vec a n} -> x :: xs ≡ y :: ys -> x ≡ y
≡-head ≡-refl = ≡-refl

≡-tail : {a : Set} {x y : a} {n : Nat} {xs ys : Vec a n} -> x :: xs ≡ y :: ys -> xs ≡ ys
≡-tail ≡-refl = ≡-refl 

≢-cons₁ : {a : Set} {x y : a} {n : Nat} {xs ys : Vec a n} -> ¬ (x ≡ y) -> ¬ (x :: xs ≡ y :: ys)
≢-cons₁ x≢y xxs≡yys = x≢y (≡-head xxs≡yys) 

≢-cons₂ : {a : Set} {x y : a} {n : Nat} {xs ys : Vec a n} -> ¬ (xs ≡ ys) -> ¬ (x :: xs ≡ y :: ys)
≢-cons₂ xs≢ys xxs≡yys = xs≢ys (≡-tail xxs≡yys)

dec-≡-Vec :  {a : Set} {n : Nat}
          -> ((x : a) -> Decidable (_≡_ x))
          -> (v : Vec a n) -> Decidable (_≡_ v)
dec-≡-Vec dec [] []        = pfl ≡-refl
dec-≡-Vec dec (x :: xs) (x' :: xs') with dec x x' | dec-≡-Vec dec xs xs'
...   | pfl x≡x' | pfl xs≡xs' = pfl (≡-cons x≡x' xs≡xs')
...   | pfr x≢x' | _          = pfr (≢-cons₁ x≢x')
...   | _        | pfr xs≢xs' = pfr (≢-cons₂ xs≢xs')