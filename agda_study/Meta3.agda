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

record One {l : Level} : Set l where
  constructor ◇
open One public

record Σ {l : Level}(S : Set l)(T : S → Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public
_×_ : {l : Level} → Set l → Set l → Set l
S × T = Σ S λ _ → T
infixr 4 _×_

𝕧_ :  forall {k l}{S : Set k}{T : S → Set k}{P : Σ S T → Set l} →
      ((s : S)(t : T s) → P (s , t)) →
      (p : Σ S T) → P p
(𝕧 p) (s , t) = p s t
infixr 1 𝕧_


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

ord : ∀{n} → Vec (Fin n) n
ord {zero} = 〈〉
ord {suc n} = zero , vmap suc (ord {n})

tabulate : ∀{n X} → (Fin n → X) → Vec X n
tabulate {n} f = vmap f ord

record EndoFunctor (F : Set → Set) : Set₁ where
  field
    map  : ∀{S T} → (S → T) → F S → F T
open EndoFunctor ⦃...⦄ public

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _⊛_
  field
    pure  : ∀ {X} → X → F X
    _⊛_   : ∀ {S T} → F (S → T) → F S → F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _⊛_ ∘ pure }
open Applicative ⦃...⦄ public

instance
  applicativeVec  : ∀ {n} → Applicative λ X → Vec X n
  applicativeVec  = record { pure = vec; _⊛_ = vapp }

endoFunctorVec  : ∀ {n} → EndoFunctor λ X → Vec X n
endoFunctorVec  = applicativeEndoFunctor

applicativeFun : ∀ {S} → Applicative λ X → S → X
applicativeFun = record
  {  pure  = λ x s → x              -- also known as K (drop environment)
  ;  _⊛_   = λ f a s → f s (a s)    -- also known as S (share environment)
  }

record Monad (F : Set → Set) : Set₁ where
  field
    return  : ∀ {X} → X → F X
    _>>=_   : ∀ {S T} → F S → (S → F T) → F T
  monadApplicative : Applicative F
  monadApplicative = record
    {  pure   = return
    ;  _⊛_  = λ ff fs → ff >>= λ f → fs >>= λ s → return (f s) }
open Monad ⦃...⦄ public

-- Exercise 1.6
instance
  monadVec : {n : ℕ} → Monad λ X → Vec X n
  monadVec = record
    { return = vec
    ; _>>=_ = λ xs f → vmap (λ i →  proj (proj (vmap f xs) i) i) ord
    }


v : Vec ℕ 3
v = 0 , 1 , 2 , 〈〉

v' = pure {λ X → Vec X 3} 0    -- 0 , 0 , 0 , 〈〉
v'' = _⊛_ {λ X → Vec X 3} {ℕ} {ℕ} (vec suc) v  -- 1 , 2 , 3 , 〈〉

v''' = _⊛_ {λ X → Vec X 3} ⦃ monadApplicative ⦄ {ℕ} {ℕ} (vec suc) v  -- 1 , 2 , 3 , 〈〉

-- Exercise 1.7
instance
  applicativeId : Applicative id
  applicativeId = record { pure = id; _⊛_ = id }

applicativeComp : ∀{F G} → Applicative F → Applicative G → Applicative (F ∘ G)
applicativeComp {F} {G} aF aG =
  record { pure = (aF .Applicative.pure) ∘ (aG .Applicative.pure)
         ; _⊛_ = lemma1 ∘ (lemma3 lemma2)
         }
  where
  lemma1 : ∀{S T} → F (G S → G T) → F (G S) → F (G T)
  lemma1 = aF .Applicative._⊛_
  lemma2 : ∀{S T} → G (S → T) → (G S → G T)
  lemma2 = aG .Applicative._⊛_
  lemma3 : ∀{S T} → (G (S → T) → (G S → G T)) → (F (G (S → T))) → (F (G S → G T))
  lemma3 = applicativeEndoFunctor {F} ⦃ aF ⦄ .EndoFunctor.map

-- Exercise 1.8
record Monoid (X : Set) : Set where
  infixr 4 _•_
  field
    ε : X
    _•_ : X → X → X
  monoidApplicative : Applicative λ _ → X
  monoidApplicative =
    record { pure = λ _ → ε
           ; _⊛_ = _•_ }
open Monoid ⦃...⦄ public


record Traversable (F : Set → Set) : Set₁ where
  field
    traverse : ∀ { G S T }⦃ AG : Applicative G ⦄ → (S → G T) → F S → G (F T)

  traversableEndoFunctor : EndoFunctor F
--  traversableEndoFunctor = record { map = traverse ⦃ applicativeId ⦄ }
  traversableEndoFunctor = record { map = traverse }
open Traversable ⦃...⦄ public

instance
  traversableVec : ∀ {n} → Traversable (λ X → Vec X n)
  traversableVec = record { traverse = vtr }
    where
      vtr : ∀ {A : Set}{n B F}⦃ _ : Applicative F ⦄ → (A → F B) → Vec A n → F (Vec B n)
      vtr ⦃ aF ⦄ f 〈〉 = pure ⦃ aF ⦄ 〈〉
      vtr ⦃ aF ⦄ f (a , as) = pure ⦃ aF ⦄ _,_ ⊛ f a ⊛ vtr ⦃ aF ⦄ f as

-- Exercise 1.10
transpose : ∀{m n X} → Vec (Vec X n) m → Vec (Vec X m) n
transpose = traverse ⦃ traversableVec ⦄ id

mn : Vec (Vec ℕ 2) 3
mn = (1 , 2 , 〈〉) , (3 , 4 , 〈〉) , (5 , 6 , 〈〉) , 〈〉

-- transpose mn = (1 , 3 , 5 , 〈〉) , (2 , 4 , 6 , 〈〉) , 〈〉
nm : Vec (Vec ℕ 3) 2
nm = transpose mn

crush : ∀ { F X Y } ⦃ TF : Traversable F ⦄ ⦃ M : Monoid Y ⦄ → (X → Y) → F X → Y
crush ⦃ M = M ⦄ = traverse { T = One }⦃ AG = monoidApplicative ⦃ M ⦄ ⦄


-- Exercise 1.11
instance
  traversableId : Traversable id
  traversableId = record { traverse = id }

traversableComp : ∀ { F G } → Traversable F → Traversable G → Traversable (F ∘ G)
traversableComp {F} {G} f g = record { traverse = traverse ⦃ f ⦄ ∘ traverse ⦃ g ⦄ }


data Two : Set where tt ff : Two
_〈?〉_ : forall {l}{P : Two → Set l} → P tt → P ff → (b : Two) → P b
(t 〈?〉 f) tt = t
(t 〈?〉 f) ff = f

_+_ : Set → Set → Set
S + T = Σ Two (S 〈?〉 T)

-- Exercise 1.12
_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ y = y
suc x +ℕ y = suc (x +ℕ y)

_×ℕ_ : ℕ → ℕ → ℕ
zero ×ℕ y = zero
suc x ×ℕ y = y +ℕ (x ×ℕ y)

record Normal : Set₁ where
  constructor _/_
  field
    Shape  : Set
    size   : Shape → ℕ
  ⟦_⟧ℕ : Set → Set
  ⟦_⟧ℕ X = Σ Shape λ s → Vec X (size s)
open Normal public
infixr 0 _/_

Vecℕ : ℕ → Normal
Vecℕ n = One / const n 

Listℕ : Normal
Listℕ = ℕ / id

Kℕ : Set → Normal
Kℕ A = A / const 0

IKℕ : Normal
IKℕ = Vecℕ 1

_+N_ : Normal → Normal → Normal
(ShF / szF) +N (ShG / szG) = (ShF + ShG) / 𝕧 szF 〈?〉 szG

_×N_ : Normal → Normal → Normal
(ShF / szF) ×N (ShG / szG) = (ShF × ShG) / 𝕧 λ f g → szF f +ℕ szG g
