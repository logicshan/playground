module LogicalFacts where

infixl 3 _∘_ 

open import Logic

_∘_ : {A B : Ω} {C : B → Ω} →
      (∀(b : B) → C b) → ∀(f : A → B) → ∀(a : A) → C(f a)

g ∘ f = λ x → g(f x)


id : {A : Ω} → A → A
id x = x


contradictory : {A : Ω} → A → ¬ A → ⊥
contradictory a f = f a

¬¬ : Ω → Ω
¬¬ A = ¬(¬ A)

¬¬-intro : {A : Ω} → A → ¬¬ A
¬¬-intro a = λ p → p a 

contra-positive : {A B : Ω} → (A → B) → ¬ B → ¬ A
contra-positive f p = p ∘ f

not-exists-implies-forall : {X : Set} → {A : X → Ω} → 
           ¬(∃(\(x : X) → A x)) → ∀(x : X) → ¬(A x)

not-exists-implies-forall f x a = f(∃-intro x a) 

forall-implies-not-exists : {X : Set} → {A : X → Ω} → 
         (∀(x : X) → ¬(A x)) → ¬(∃(\(x : X) → A x)) 

forall-implies-not-exists f (∃-intro x a) = f x a
