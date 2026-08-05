
module Unifying where

data Σ (a : Set) (P : a → Set) : Set where
  _,_ : (x : a) (w : P x) → Σ a P

codata ∞_ (a : Set) : Set where
  ♯_ : a → ∞ a

♭ : ∀{a} → ∞ a → a
♭ (♯ a) = a

data Acc {a : Set} (_<_ : a → a → Set) : a → Set where
  acc : ∀{x} → (∀{y} → y < x → Acc _<_ y) → Acc _<_ x

wfi : ∀{a} {P : a → Set} {_<_ : a → a → Set}
    → (x : a) → (∀ y → (∀ z → z < y → P z) → P y) → Acc _<_ x → P x
wfi {_} {P} {_<_} x Φ (acc pf) = Φ x (λ y y<x → wfi y Φ (pf y<x))

data _≜_ {a : Set} (x : a) : a → Set where
  ≜-refl : x ≜ x

data ℕ : Set where
  zero : ℕ
  1+_  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     1+_  #-}

data _≤-ℕ_ : ℕ → ℕ → Set where
  0≤  : ∀{n} → 0 ≤-ℕ n
  s≤s : ∀{m n} → m ≤-ℕ n → 1+ m ≤-ℕ 1+ n

_<-ℕ_ : ℕ → ℕ → Set
m <-ℕ n = 1+ m ≤-ℕ n

trans-ℕ : ∀{i j k} → i ≤-ℕ j → j ≤-ℕ k → i ≤-ℕ k
trans-ℕ 0≤        j≤k       = 0≤
trans-ℕ (s≤s i≤j) (s≤s j≤k) = s≤s (trans-ℕ i≤j j≤k)

acc-<-ℕ : ∀{m} → Acc _<-ℕ_ m
acc-<-ℕ {m} = acc (λ {n} n<m → aux m n n<m)
 where
 aux : ∀ m n → n <-ℕ m → Acc _<-ℕ_ n
 aux 0      n ()
 aux (1+ m) zero (s≤s n≤m) = acc (λ ())
 aux (1+ m) (1+ n) (s≤s n≤m) = acc (λ n'<n → aux m _ (trans-ℕ n'<n n≤m))

infixr 40 _::_
data List (a : Set) : Set where
  []   : List a
  _::_ : a → List a → List a

data Stream (a : Set) : Set where
  _≺_ : a → ∞ Stream a → Stream a

take : ∀{a} → ℕ → Stream a → List a
take 0       _       = []
take (1+ n) (e ≺ es) = e :: take n (♭ es)

record Equiv (a : Set) (_≈_ : a → a → Set) : Set where
  field
    refl  : ∀{x} → x ≈ x
    symm  : ∀{x y} → x ≈ y → y ≈ x
    trans : ∀{x y z} → x ≈ y → y ≈ z → x ≈ z

ListEq : ∀{a} → Equiv (List a) _≜_
ListEq {a} = record { refl  = ≜-refl
                    ; symm  = s
                    ; trans = t
                    }
 where
 s : ∀{l l' : List a} → l ≜ l' → l' ≜ l
 s ≜-refl = ≜-refl
 t : ∀{l l' l'' : List a} → l ≜ l' → l' ≜ l'' → l ≜ l''
 t ≜-refl ≜-refl = ≜-refl

record OFE : Set1 where
  field
    carrier : Set
    domain  : Set
    _<_     : carrier → carrier → Set
    wf      : ∀ x → Acc _<_ x
    _≡⟨_⟩_  : domain → carrier → domain → Set
    eq      : ∀ a → Equiv domain λ x y → x ≡⟨ a ⟩ y
  
  _≡_ : domain → domain → Set
  x ≡ y = ∀ a → x ≡⟨ a ⟩ y

StreamOFE : ∀ a → OFE
StreamOFE a = record { carrier = ℕ
                     ; domain  = Stream a
                     ; _<_     = _<-ℕ_
                     ; wf      = λ n → acc-<-ℕ {n}
                     ; _≡⟨_⟩_  = λ l n r → take n l ≜ take n r
                     ; eq      = StreamEq
                     }
 where
 StreamEq : ∀ n → Equiv (Stream a) λ l r → take n l ≜ take n r
 StreamEq n = record { refl  = Equiv.refl  ListEq
                     ; symm  = Equiv.symm  ListEq
                     ; trans = Equiv.trans ListEq
                     }

Injective : ∀{a b} → (a → b) → Set
Injective f = ∀ x y → f x ≜ f y → x ≜ y

_⊆_ : Set → Set → Set
b ⊆ a = Σ (b → a) Injective

Preds : {a : Set} → (a → a → Set) → a → Set
Preds {a} _<_ x = Σ a (λ y → y < x)

module Coherence (O : OFE) where
  open OFE O

  Coherent : (i : Set) → i ⊆ carrier → (i → domain) → Set
  Coherent i (inj , _) x = ∀ (a' a : i) → inj a' < inj a → x a' ≡⟨ inj a' ⟩ x a

  Limit : (i : Set) → i ⊆ carrier → (i → domain) → domain → Set
  Limit i (inj , _) x y = ∀ (a : i) → x a ≡⟨ inj a ⟩ y

















