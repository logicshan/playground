{-# OPTIONS --no-termination-check #-}

module IRDataHierarchy where

open import Meta

record Lifted (A : Set) : Set₁ where
  constructor lif
  field
    fil : A

open Lifted

-- Descriptions of indexed inductive-recursive types seen here:
-- http://www.e-pig.org/darcsweb?r=Pig09;a=headblob;f=/models/Alg-IIR.agda
mutual
  data Descr (I : Set₁) (J : I → Set₁) : Set₁ where
    var : I → Descr I J
    con : Set → Descr I J
    _*_ : (S : Descr I J) → (T : Deco S → Descr I J) → Descr I J
    _>_ : (S : Set) → (T : S → Descr I J) → Descr I J

  Deco : ∀{I J} → Descr I J → Set₁
  Deco {J = J} (var i) = J i
  Deco         (con A) = Lifted A
  Deco         (S * T) = Σ (Deco S) \s → Deco (T s)
  Deco         (S > T) = (s : S) → Deco (T s)

mutual
  Func : ∀{I J} → Descr I J → (X : I → Set) (d : X -:> J) → Set
  Func (var i) X d = X i
  Func (con A) X d = A
  Func (S * T) X d = Σ (Func S X d) \s → Func (T (deco S X d s)) X d
  Func (S > T) X d = (s : S) → Func (T s) X d

  deco : ∀{I J}
         → (D : Descr I J) (X : I → Set) (d : X -:> J) → Func D X d → Deco D
  deco (var i) X d x       = d i x
  deco (con A) X d a       = lif a
  deco (S * T) X d (s , t) = s' , t'
    where s' = deco S X d s
          t' = deco (T s') X d t
  deco (S > T) X d f       = \s → deco (T s) X d (f s)

mutual
  data Fix {I J} (F : I → Descr I J) (d : (Deco ∘ F) -:> J) (i : I) : Set where
    <_> : Func (F i) (Fix F d) decode → Fix F d i

  -- fails to termination check, unsurprisingly
  decode : ∀{I J} {F : I → Descr I J} {d : (Deco ∘ F) -:> J}
         → Fix F d -:> J
  decode {I}{J}{F}{d} i < xs > = d i (deco (F i) (Fix F d) decode xs)

module Build (U : Set) (T : U → Set)
             (Desc : (i : U) → (j : T i → U) → Set) where
  mutual
    data Φ : Set where
      Π    : (s : Φ) (f : Θ s → Φ) → Φ
      u    : Φ
      t    : U → Φ
      desc : ∀(i : U) (j : T i → U) → Φ
      μ    : ∀{i j} → (f : Θ i → Δ i j)
                    → (d : ∀ x → Δeco (f x) → Θ (j x))
                    → Θ i → Φ
    Θ : Φ → Set
    Θ (Π s f)    = (x : Θ s) → Θ (f x)
    Θ u          = U
    Θ (t s)      = T s
    Θ (desc i j) = Desc i j
    Θ (μ f d x)  = Fix (\x → ⟦ f (fil x) ⟧)
                       (\i X → lif (d (fil i) ⟧ X ⟦))
                       (lif x)

    data Δ (i : Φ) (j : Θ i → Φ) : Set where
      var : Θ i → Δ i j
      con : Φ → Δ i j
      _*_ : (S : Δ i j) → (F : Δeco S → Δ i j) → Δ i j
      _>_ : (s : Φ) (f : Θ s → Δ i j) → Δ i j

    Δeco : ∀{i j} → Δ i j → Set
    Δeco {j = j} (var i) = Θ (j i)
    Δeco         (con a) = Θ a
    Δeco         (S * F) = Σ (Δeco S) \s → Δeco (F s)
    Δeco         (s > f) = (x : Θ s) → Δeco (f x)

    ⟦_⟧ : ∀{i j} → Δ i j → Descr (Lifted (Θ i)) (Lifted ∘ Θ ∘ j ∘ fil)
    ⟦ var i ⟧  = var (lif i)
    ⟦ con a ⟧  = con (Θ a)
    ⟦_⟧{i}{j} (S * F)  = ⟦ S ⟧ * \D → ⟦ F (⟧_⟦ {i}{j} D) ⟧
    ⟦ s > f ⟧  = Θ s > \x → ⟦ f x ⟧

    ⟧_⟦ : ∀{i j} → {D : Δ i j} → Deco ⟦ D ⟧ → Δeco D
    ⟧_⟦ {D = var i} X = fil X
    ⟧_⟦ {D = con a} X = fil X
    ⟧_⟦ {i}{j}{D = S * F} (x , y) = x' , y'
      where x' = ⟧_⟦ {i} {j} {S} x
            y' = ⟧_⟦ {i} {j} {F x'} y
    ⟧_⟦ {i}{j}{D = s > f} X = \x → ⟧_⟦ {i}{j}{f x} (X x)

  _⇒_ : Φ → Φ → Φ
  a ⇒ b = Π a \_ → b

  dec : ∀{i j} {f : Θ i → Δ i j} {d : ∀ x → Δeco (f x) → Θ (j x)}
      → Θ (Π i \x → μ f d x ⇒ j x)
  dec {i}{j}{f}{d} x y = fil (decode {Lifted (Θ i)}
                                     {\z → Lifted (Θ (j (fil z)))}
                                     {\z → ⟦ f (fil z) ⟧}
                                     {\z X → lif (d (fil z) 
                                                    (⟧_⟦ {i}{j}{f (fil z)} X))}
                                     (lif x) y)

mutual
  U' : ℕ → Set
  U' zero    = ⊥
  U' (suc n) = Build.Φ (U' n) (T' n) (Desc' n)

  T' : (n : ℕ) → U' n → Set
  T' zero    ()
  T' (suc n) s = Build.Θ (U' n) (T' n) (Desc' n) s

  Desc' : (n : ℕ) → (i : U' n) (j : T' n i → U' n) → Set
  Desc' zero    i j = ⊥
  Desc' (suc n) i j = Build.Δ (U' n) (T' n) (Desc' n) i j

  DUp' : (n : ℕ) {i : U' n} {j : T' n i → U' n}
      → Desc' n i j → Descr (Lifted (T' n i)) (Lifted ∘ T' n ∘ j ∘ fil)
  DUp' zero    ()
  DUp' (suc n) D = Build.⟦_⟧ (U' n) (T' n) (Desc' n) D

  Dec' : (n : ℕ) → {i : U' n} {j : T' n i → U' n} → Desc' n i j → Set
  Dec' zero    ()
  Dec' (suc n) D = Build.Δeco (U' n) (T' n) (Desc' n) D
  
  DDn' : (n : ℕ) {i : U' n} {j : T' n i → U' n} {D : Desc' n i j}
      → Deco (DUp' n D) → Dec' n D
  DDn' zero {D = ()} _
  DDn' (suc n) {i}{j}{D} X = Build.⟧_⟦ (U' n) (T' n) (Desc' n) {i}{j}{D} X

  dec' : (n : ℕ)
       → {i : U' n} {j : T' n i → U' n} {f : T' n i → Desc' n i j}
         {d : ∀ x → Dec' n (f x) → T' n (j x)}
       → (x : T' n i) → Fix {Lifted $ T' n i}
                            {Lifted ∘ T' n ∘ j ∘ fil}
                            (DUp' n ∘ f ∘ fil)
                            (\i D → lif (d (fil i) (DDn' n D)))
                            (lif x)
       → T' n (j x)
  dec' zero {i = ()} _ _
  dec' (suc n) {i}{j}{f}{d} x y
     = Build.dec (U' n) (T' n) (Desc' n) {i}{j}{f}{d} x y

U : ℕ → Set
U n = U' (suc n)

T : {n : ℕ} → U n → Set
T {n} = T' (suc n)

Desc : (n : ℕ) (i : U n) (j : T i → U n) → Set
Desc n = Desc' (suc n)

DUp : {n : ℕ} {i : U n} {j : T i → U n} → Desc n i j
    → Descr (Lifted (T i)) (Lifted ∘ T ∘ j ∘ fil)
DUp {n} = DUp' (suc n)

Dec : {n : ℕ} {i : U n} {j : T i → U n} → Desc n i j → Set
Dec {n} = Dec' (suc n)

DDn : {n : ℕ} {i : U n} {j : T i → U n} {D : Desc n i j}
    → Deco (DUp D) → Dec D
DDn {n}{i}{j}{D} = DDn' (suc n) {i}{j}{D}

dec : {n : ℕ} {i : U n} {j : T i → U n} {f : T i → Desc n i j}
      {d : ∀ x → Dec (f x) → T (j x)}
    → (x : T i) → Fix {Lifted $ T i}
                      {Lifted ∘ T ∘ j ∘ fil}
                      (DUp ∘ f ∘ fil)
                      (\z D → lif (d (fil z) (DDn {n}{i}{j}{f $ fil z} D)))
                      (lif x)
    → T (j x)
dec {n}{i}{j}{f}{d} = dec' (suc n) {i}{j}{f}{d}
