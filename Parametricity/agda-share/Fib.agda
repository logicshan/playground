
module Fib where

  data ⊥ : Set where

  infix 30 ¬_
  ¬_ : Set → Set
  ¬ a = a → ⊥

  record ⊤ : Set where

  infixr 40 _⊎_
  data _⊎_ (a b : Set) : Set where
    inl : a → a ⊎ b
    inr : b → a ⊎ b

  data Maybe (a : Set) : Set where
    nothing : Maybe a
    just    : a → Maybe a
  
  infixr 30 _,_
  data Σ (a : Set) (P : a → Set) : Set where
    _,_ : (x : a) (w : P x) → Σ a P


  π₁ : ∀{a} {P : a → Set} → Σ a P → a
  π₁ (x , _) = x

  π₂ : ∀{a} {P : a → Set} → (p : Σ a P) → P (π₁ p)
  π₂ (_ , w) = w


  infixr 30 _×_
  _×_ : Set → Set → Set
  a × b = Σ a (λ _ → b)


  data Acc {a : Set} (_<_ : a → a → Set) : a → Set where
    acc : ∀{x} → (∀{y} → y < x → Acc _<_ y) → Acc _<_ x

  wf-induction : ∀{a : Set} {_<_ : a → a → Set} {P : a → Set}
               →  (∀{y} → (∀{z} → z < y → P z) → P y) → {x : a} → Acc _<_ x → P x
  wf-induction Φ (acc f) = Φ (λ z<x → wf-induction Φ (f z<x))

  infixr 50 _::_
  data List (a : Set) : Set where
    []   : List a
    _::_ : a → List a → List a

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ -> ℕ
  {-# BUILTIN NATURAL ℕ    #-}
  {-# BUILTIN ZERO    zero #-}
  {-# BUILTIN SUC     suc  #-}

  infixl 50 _+_
  _+_ : ℕ -> ℕ -> ℕ
  zero    + n = n
  (suc m) + n = suc (m + n)
  {-# BUILTIN NATPLUS _+_ #-}

  infixl 50 _-_
  _-_ : ℕ → ℕ → Maybe ℕ
  m     - zero  = just m
  zero  - suc n = nothing
  suc m - suc n = m - n

  infix 45 _≤_
  data _≤_ : ℕ → ℕ → Set where
    z≤k : ∀{k} → zero ≤ k
    s≤s : ∀{m n} → m ≤ n → suc m ≤ suc n
  
  infix 45 _<_
  _<_ : ℕ → ℕ → Set
  m < n = suc m ≤ n

  ≤-refl : ∀{i} → i ≤ i
  ≤-refl {zero}  = z≤k
  ≤-refl {suc i} = s≤s ≤-refl

  ≤-trans : ∀{i j k} → i ≤ j → j ≤ k → i ≤ k
  ≤-trans z≤k       j≤k = z≤k
  ≤-trans (s≤s i≤j) (s≤s j≤k) = s≤s (≤-trans i≤j j≤k)

  ≤-step : ∀{i j} → i ≤ j → i ≤ suc j
  ≤-step {zero}  _ = z≤k
  ≤-step {suc i} (s≤s i≤j) = s≤s (≤-step i≤j)

  <-step : ∀{i j} → suc i < j → i < j
  <-step (s≤s i<j) = ≤-step i<j

  <-trans : ∀{i j k} → i < j → j < k → i < k
  <-trans i<j j<k = <-step (≤-trans (s≤s i<j) j<k)

  ≤-+ : ∀{i j} → j ≤ i + j
  ≤-+ {zero}  = ≤-refl
  ≤-+ {suc i} = ≤-step (≤-+ {i})

  ¬n<n : ∀{n} → ¬ n < n
  ¬n<n {zero}  ()
  ¬n<n {suc n} (s≤s n<n) = ¬n<n n<n

  dec-≤ : ∀ m n → m < n ⊎ n ≤ m
  dec-≤ zero    zero    = inr z≤k
  dec-≤ zero    (suc _) = inl (s≤s z≤k)
  dec-≤ (suc m) zero    = inr z≤k
  dec-≤ (suc m) (suc n) with dec-≤ m n
  ...         | inl m<n = inl (s≤s m<n)
  ...         | inr n≤m = inr (s≤s n≤m)

  wf-< : ∀{n} → Acc _<_ n
  wf-< {n} = acc (λ {m} → aux n m)
   where
   aux : ∀ n m → m < n → Acc _<_ m
   aux n       zero    m<n = acc (λ ())
   aux zero    (suc m) ()
   aux (suc n) (suc m) (s≤s m<n) = acc (λ {m'} m'<m → aux n m' (≤-trans m'<m m<n))

  wf-unfold : ∀{a s} {_<_ : s → s → Set}
            → ((s₀ : s) → Maybe (a × Σ s (λ s₁ → s₁ < s₀)))
            → (t : s) → Acc _<_ t → List a
  wf-unfold {a} {s} {_<_} step seed Acc = wf-induction Φ {seed} Acc
   where
   P : s → Set
   P _ = List a
   Φ : ∀{y} → (∀{z} → z < y → P z) → P y
   Φ {y} rec with step y
   ...       | nothing            = []
   ...       | just (x , z , z<y) = x :: rec {z} z<y

  _`<`_ : Maybe ℕ → Maybe ℕ → Set
  _       `<` nothing = ⊥
  nothing `<` just _  = ⊤
  just m  `<` just n  = m < n

  `<`-trans : ∀{i j k} → i `<` j → j `<` k → i `<` k
  `<`-trans {i}       {j}       {nothing} i`<`j ()
  `<`-trans {nothing} {j}       {just k}  i`<`j j`<`k = _
  `<`-trans {just i}  {nothing} {just k}  ()    j`<`k
  `<`-trans {just i}  {just j}  {just k}  i`<`j j`<`k = <-trans i`<`j j`<`k

  wf-`<` : ∀{n} → Acc _`<`_ n
  wf-`<` {nothing} = acc λ()
  wf-`<` {just n}  = wf-induction Φ wf-<
   where
   P : ℕ → Set
   P n = Acc _`<`_ (just n)
   Φ : ∀{y} → (∀{z} → z < y → P z) → P y
   Φ {y} rec = acc aux
    where
    aux : ∀{z} → z `<` just y → Acc _`<`_ z
    aux {nothing} z`<`jy = acc λ()
    aux {just z}  z<y    = rec {z} z<y

  _<⟨_⟩_ : ℕ → ℕ → ℕ → Set
  x <⟨ n ⟩ y = n - x `<` n - y

  _<-×_ : ∀{a} → ℕ × a → ℕ × a → Set
  p <-× p' = π₁ p < π₁ p'

  wf-<-× : ∀{a} {tup : ℕ × a} → Acc (_<-×_ {a}) tup
  wf-<-× {a} {n , x} = wf-induction {P = P} Φ {n} wf-< {x}
   where
   P : ℕ → Set
   P n = ∀{x : a} → Acc _<-×_ (n , x)
   Φ : ∀{y} → (∀{z} → z < y → P z) → P y
   Φ {y} rec {x} = acc aux
    where
    aux : {tup : ℕ × a} → π₁ tup < y → Acc _<-×_ tup
    aux {z , x} z<y = rec z<y


{-
  _<⟨_⟩_ : ℕ → ℕ → ℕ → Set
  i <⟨ n ⟩ j = n - i < n - j

  lemma₁ : ∀{i j} → j < i → i - suc j < i
  lemma₁ {zero}  {j} ()
  lemma₁ {suc i} {zero}  (s≤s j<i) = ≤-refl
  lemma₁ {suc i} {suc j} (s≤s j<i) = ≤-trans ind (≤-step ≤-refl)
   where
   ind : i - suc j < i
   ind = lemma₁ j<i


  swap-<₀ : ∀{n i j} → i < j → j ≤ n → j <⟨ n ⟩ i
  swap-<₀ {n}     {i}     {zero}  ()        j≤n
  swap-<₀ {n}     {zero}  {suc j} i<j       j≤n       = lemma₁ j≤n
  swap-<₀ {zero}  {suc i} {suc j} i<j       ()
  swap-<₀ {suc n} {suc i} {suc j} (s≤s i<j) (s≤s j≤n) = swap-<₀ i<j j≤n
-}







