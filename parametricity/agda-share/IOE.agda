{-# OPTIONS --type-in-type #-}

-- A term/EDSL model of Haskell's IO type.
--
-- Set : Set is used instead of impredicativity, because Agda doesn't
-- have the latter. I promise to try not to write any paradoxes.

module IOE where

open import Data.Char
open import Data.List using (List ; _∷_ ; [])
open import Data.Nat
open import Data.String
open import Data.Unit

open import Relation.Binary.PropositionalEquality

postulate
  -- An abstract type of MVars. The details don't really matter for what
  -- we're doing here.
  MVar : Set → Set

  -- Imagine we have a way of showing anything, for ease.
  show : ∀{A} → A → String

mutual
  -- This separation is intended to ensure that we can only represent
  -- normal forms (so to speak) of IO computations up to the monad laws.
  -- 1) pure x :>>= f is a type error.
  -- 2) As is (m :>>= f) :>>= g.
  -- 3) If m :>>= pure inhabits IO a, then m itself does not, so the
  --    the former is taken to be the canonical form.
  --
  -- This declaration is easily translated to GADTs in GHC.
  data PreIO : Set → Set where
    get    : PreIO Char
    put    : Char → PreIO ⊤
    fork   : ∀{A} → IO A → PreIO ⊤
    mkvar  : ∀{A} → PreIO (MVar A)
    fill   : ∀{A} → MVar A → A → PreIO ⊤
    take   : ∀{A} → MVar A → PreIO A

  data IO (A : Set) : Set where
    pure    : A → IO A
    _:>>=_  : ∀{B} → PreIO B → (B → IO A) → IO A

postulate
  -- We need point-wise equality to entail equality of functions below.
  ext : ∀{A B : Set} → (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g

-- Lifting the PreIO stuff to actual IO actions
getChar : IO Char
getChar = get :>>= pure

putChar : Char → IO ⊤
putChar c = put c :>>= pure

forkIO : ∀{A} → IO A → IO ⊤
forkIO m = fork m :>>= pure

newMVar : ∀{A} → IO (MVar A)
newMVar = mkvar :>>= pure

takeMVar : ∀{A} → MVar A → IO A
takeMVar m = take m :>>= pure

infix 35 _:=_
_:=_ : ∀{A} → MVar A → A → IO ⊤
r := v = fill r v :>>= pure

-- The monad operations
return : ∀{A} → A → IO A
return = pure

infixl 30 _>>=_
_>>=_ : ∀{A B} → IO A → (A → IO B) → IO B
pure x     >>= f = f x
(m :>>= g) >>= f = m :>>= λ x -> g x >>= f

infixl 30 _>>_
_>>_ : ∀{A B} → IO A → IO B → IO B
m₁ >> m₂ = m₁ >>= λ _ → m₂

putChars : List Char → IO ⊤
putChars []       = pure _
putChars (c ∷ cs) = putChar c >> putChars cs

putStr : String → IO ⊤
putStr s = putChars (toList s)

putStrLn : String → IO ⊤
putStrLn s = putStr s >> putChar '\n'

print : ∀{A} → A → IO ⊤
print x = putStrLn (show x)

-- Proof of the monad laws
left-id : ∀{A B} (x : A) (f : A → IO B) → (return x >>= f) ≡ f x
left-id x f = refl

right-id : ∀{A} (m : IO A) → (m >>= return) ≡ m
right-id (pure x)   = refl
right-id (p :>>= g) = cong (λ f → p :>>= f) 
                           (ext (λ x → g x >>= pure) g (λ x → right-id (g x)))

assoc : ∀{A B C} (m : IO A) (f : A → IO B) (g : B → IO C)
      → (m >>= f >>= g) ≡ (m >>= λ x → f x >>= g)
assoc (pure x)   f g = refl
assoc (p :>>= h) f g = cong (λ k → p :>>= k)
                            (ext (λ x → h x >>= f >>= g)
                                 (λ x → h x >>= λ y → f y >>= g)
                                 (λ x → assoc (h x) f g))

-- An IO computation with concurrency.
main : IO ⊤
main = newMVar >>= \r₁ →
       newMVar >>= \r₂ →
       newMVar >>= \r₃ →
       let other : IO ⊤
           other = takeMVar r₁ >>= \x →
                   r₂ := x >>
                   r₃ := (x + 1)
       in forkIO other >>
          r₁ := 5 >>
          takeMVar r₂ >>= \x →
          takeMVar r₃ >>= \y →
          print (x + y) >>
          putStrLn "Done!"

