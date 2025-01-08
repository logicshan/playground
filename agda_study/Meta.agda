open import Agda.Primitive using (Level)

id : ∀ {k}{X : Set k} → X → X
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x

_∘_ : ∀ {i j k}
        {A : Set i}{B : A → Set j}{C : (a : A) → B a → Set k} →
        (f : {a : A}(b : B a) → C a b) →
        (g : (a : A) → B a) →
        (a : A) → C a (g a)
f ∘ g = λ a → f (g a)

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

infixr 9 _∘_

record Sg {l : Level}(S : Set l)(T : S → Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_×_ : {l : Level} → Set l → Set l → Set l
S × T = Sg S λ _ → T
infixr 4 _×_


data List (X : Set) : Set where
  〈〉    :               List X
  _,_   : X → List X →  List X

infixr 4 _,_

data ℕ : Set where
  zero  :     ℕ
  suc   : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

length : {X : Set} → List X → ℕ
length 〈〉 = zero
length (x , xs) = suc (length xs)

data Vec (X : Set) : ℕ → Set where
  〈〉   :                          Vec X zero
  _,_  : {n : ℕ} → X → Vec X n →  Vec X (suc n)

zip' : ∀{n S T} → Vec S n → Vec T n → Vec (S × T) n
zip' 〈〉 〈〉 = 〈〉
zip' (s , ss) (t , ts) = (s , t) , zip' ss ts

-- Exercise 1.1
vec : ∀ {n X} → X → Vec X n
vec {zero} x = 〈〉
vec {suc n} x = x , vec x

-- Exercise 1.2
vapp : ∀ {n S T} → Vec (S → T) n → Vec S n → Vec T n
vapp 〈〉 〈〉 = 〈〉
vapp (f , fs) (s , ss) = f s , vapp fs ss

-- Exercise 1.3
vmap : ∀ {n S T} → (S → T) → Vec S n → Vec T n
vmap f 〈〉 = 〈〉
vmap f (x , ss) = f x , vmap f ss

-- Exercise 1.4
zip : ∀{n S T} → Vec S n → Vec T n → Vec (S × T) n
--zip ss ts = vapp (vapp (vec _,_) ss) ts
--zip ss = vapp (vapp (vec _,_) ss)
zip = vapp ∘ vapp (vec _,_)

-- Exercise 1.5
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

proj : ∀{n X} → Vec X n → Fin n → X
proj (x , _) zero = x
proj (_ , xs) (suc i) = proj xs i

tabulate : ∀{n X} → (Fin n → X) → Vec X n
tabulate {n} f = vmap f ord
  where
  ord : ∀{n} → Vec (Fin n) n
  ord {zero} = 〈〉
  ord {suc n} = zero , vmap suc (ord {n})
  
record EndoFunctor (F : Set → Set) : Set₁ where
  field
    map  : ∀{S T} → (S → T) → F S → F T
open EndoFunctor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _⊛_
  field
    pure    : ∀ {X} → X → F X
    _⊛_   : ∀ {S T} → F (S → T) → F S → F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _⊛_ ∘ pure }
open Applicative {{...}} public

applicativeVec  : ∀ {n} → Applicative λ X → Vec X n
applicativeVec  = record { pure = vec; _⊛_ = vapp }
endoFunctorVec  : ∀ {n} → EndoFunctor λ X → Vec X n
endoFunctorVec  = applicativeEndoFunctor ⦃ applicativeVec ⦄

applicativeFun : ∀ {S} → Applicative λ X → S → X
applicativeFun = record
  {  pure  = λ x s → x              -- also known as K (drop environment)
  ;  _⊛_   = λ f a s → f s (a s)    -- also known as S (share environment)
  }


applicativeId : Applicative id
applicativeId = record { pure = id; _⊛_ = id }

record Monad (F : Set → Set) : Set₁ where
  field
    return  : ∀ {X} → X → F X
    _>>=_   : ∀ {S T} → F S → (S → F T) → F T
  monadApplicative : Applicative F
  monadApplicative = record
    {  pure   = return
    ;  _⊛_  = λ ff fs → ff >>= λ f → fs >>= λ s → return (f s) }
open Monad {{...}} public

-- Exercise 1.6
{-
monadVec : {n : ℕ} → Monad λ X → Vec X n
monadVec = record
  { return = vec
  ; _>>=_ = λ xs f → vmap {!!} (vmap f xs) 
  }
-}
monadVec : {n : ℕ} → Monad λ X → Vec X n
monadVec = record
  { return = vec
  ; _>>=_ = λ xs f → diagonal (vmap f xs)
  }
  where
    diagonal : ∀ {X n} → Vec (Vec X n) n → Vec X n
    diagonal 〈〉 = 〈〉
    diagonal ((x , _) , xss) = x , diagonal (vmap tail xss)
      where
        tail : ∀ {X n} → Vec X (suc n) → Vec X n
        tail (_ , xs) = xs
v : Vec ℕ 3
v = 0 , 1 , 2 , 〈〉

v' = pure {λ X → Vec X 3} ⦃ applicativeVec ⦄ 0    -- 0 , 0 , 0 , 〈〉
v'' = _⊛_ {λ X → Vec X 3} ⦃ applicativeVec ⦄ {ℕ} {ℕ} (vec suc) v  -- 1 , 2 , 3 , 〈〉

v''' = _⊛_ {λ X → Vec X 3} ⦃ monadApplicative {λ X → Vec X 3} ⦃ monadVec ⦄ ⦄ {ℕ} {ℕ} (vec suc) v  -- 1 , 2 , 3 , 〈〉
