
module Logic where

data ⊥ : Prop where

naughty : {a : Set} -> ⊥ -> a
naughty ()

record ⊤ : Prop where
True : ⊤
True = record {}

infix 50 ¬_
¬_ : Prop -> Prop
¬ P = P -> ⊥

infixl 40 _∨_
data _∨_ (P Q : Prop) : Prop where
  pfl : P -> P ∨ Q
  pfr : Q -> P ∨ Q

infixl 35 _∧_
data _∧_ (P Q : Prop) : Prop where
  _^_ : P -> Q -> P ∧ Q

contradict-l : {P Q : Prop} -> ¬ P -> ¬ (P ∧ Q)
contradict-l ¬P (P ^ _) = ¬P P

contradict-r : {P Q : Prop} -> ¬ Q -> ¬ (P ∧ Q)
contradict-r ¬Q (_ ^ Q) = ¬Q Q

Decidable : {a : Set} -> (a -> Prop) -> Prop
Decidable P = forall x -> P x ∨ ¬ P x

data _≡_ {a : Set} (x : a) : a -> Prop where
  ≡-refl : x ≡ x

data Inspect {a : Set} (x : a) : Set where
  it : (y : a) -> (w : y ≡ x) -> Inspect x

inspect : {a : Set} -> (x : a) -> Inspect x
inspect x = it x ≡-refl

≡-resp : {a : Set} {x y : a} -> (P : a -> Prop) -> x ≡ y -> P x -> P y
≡-resp P ≡-refl Px = Px

≡-symm : {a : Set} {x y : a} -> x ≡ y -> y ≡ x
≡-symm ≡-refl = ≡-refl
