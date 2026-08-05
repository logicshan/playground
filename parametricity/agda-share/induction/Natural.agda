
module Natural where

data ⊥ : Set where

record ⊤ : Set where

True : ⊤
True = record {}

data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO    z #-}
{-# BUILTIN SUC     s #-}

infixl 40 _+_
_+_ : ℕ → ℕ → ℕ
z   + n = n
s m + n = s (m + n)
{-# BUILTIN NATPLUS _+_ #-}

infixl 50 _*_
_*_ : ℕ → ℕ → ℕ
z   * _ = z
s m * n = n + m * n
{-# BUILTIN NATTIMES _*_ #-}

data _≤_ : ℕ → ℕ → Set where
  z≤m : ∀{m} → z ≤ m
  s≤s : ∀{m n} → m ≤ n → s m ≤ s n

≤-trans : ∀{i j k} → i ≤ j → j ≤ k → i ≤ k
≤-trans z≤m       _         = z≤m
≤-trans (s≤s i≤j) (s≤s j≤k) = s≤s (≤-trans i≤j j≤k)

_<_ : ℕ → ℕ → Set
m < n = s m ≤ n

induction : ∀{P : ℕ → Set} → P 0 → (∀ m → P m → P (s m)) → (n : ℕ) → P n
induction pz ps z     = pz
induction pz ps (s n) = ps n (induction pz ps n)

wf-induction : ∀{P : ℕ → Set} → (∀ n → (∀ m → m < n → P m) → P n) → (n : ℕ) → P n
wf-induction {P} p n = p n (wf-aux n)
 where
 wf-aux : ∀ n m → m < n → P m
 wf-aux z     m     ()
 wf-aux (s n) z     (s≤s m≤n) = p z (λ _ ())
 wf-aux (s n) (s m) (s≤s m≤n) = p (s m) (λ m' sm'≤sm → wf-aux n m' (≤-trans sm'≤sm m≤n))

_≤'_ : ℕ → ℕ → Set
z   ≤' _   = ⊤
s _ ≤' z   = ⊥
s m ≤' s n = m ≤' n

_<'_ : ℕ → ℕ → Set
m <' n = s m ≤' n

≤'-s : ∀{m n} → m ≤' n → s m ≤' s n
≤'-s m≤'n = m≤'n

≤'-trans : ∀{i j k} → i ≤' j → j ≤' k → i ≤' k
≤'-trans {z} i≤'j j≤'k = _
≤'-trans {s i} {z} () j≤'k
≤'-trans {s i} {s j} {z} i≤'j ()
≤'-trans {s i} {s j} {s k} i≤'j j≤'k = ≤'-trans i≤'j j≤'k

wf-induction' : ∀{P : ℕ → Set} → (∀ n → (∀ m → m <' n → P m) → P n) → (n : ℕ) → P n
wf-induction' {P} p n = p n (wf-aux' n)
 where
 wf-aux' : ∀ n m → m <' n → P m
 wf-aux' z     m ()
 wf-aux' (s n) z     m<'n = p z (λ _ ())
 wf-aux' (s n) (s m) m<'n = p (s m) (λ m' sm'≤sm → wf-aux' n m' (≤'-trans {s m'} {s m} {n} sm'≤sm m<'n))