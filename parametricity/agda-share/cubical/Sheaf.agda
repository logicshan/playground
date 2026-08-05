
module Sheaf where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma hiding (Σ)

variable
  ℓ ℓ' : Level
  T : Type ℓ
  P : T -> Type ℓ

module Base (Q : Type) (R : Q -> Type) where
  -- A sheaf is like an algebra for the 'generic effect' with type:
  --
  --     (q : Q) -> R q
  --
  -- with the additional proviso that there aren't really effects,
  -- per se, because an 'effect' whose result we ignore is equivalent
  -- to no effect at all. So, the 'effects' are more akin to accessing
  -- some implicit, immutable knowledge store than something like
  -- state, or catchable exceptions.
  --
  -- Actual sheaves requires that R q be propositional, as well, so
  -- any query can be answered in at most one way, up to equivalence.
  --
  -- Note: this can also be imagined as a Q-indexed family of generic
  -- effects with type:
  --
  --     ⊤ -> R q
  --
  -- To make it fit in better with the usual presentation.
  record isSheaf (T : Type ℓ) : Type ℓ where
    field
      ask : (q : Q) -> (R q -> T) -> T
      irr : ∀ q t -> ask q (const t) ≡ t

  Sheaf : (ℓ : Level) -> Type (ℓ-suc ℓ)
  Sheaf ℓ = TypeWithStr ℓ isSheaf

module Lemmas
  {Q : Type} {R : Q -> Type}
  (Rp : ∀ q → isProp (R q))
  where
  open Base Q R
  open Iso

  module _ (T-sh : Base.isSheaf Q R T) where
    open isSheaf T-sh

    const-lemma₁ : ∀{q} r (k : R q -> T) → k ≡ const (k r)
    const-lemma₁ r k = funExt (cong k ∘ flip (Rp _) r)

    -- If R q holds via r, then querying the implicit store gives
    -- an answer equivalent to r.
    ans : ∀ q k r → ask q k ≡ k r
    ans q k r i =
      hcomp (λ j → λ where
          (i = i0) → ask q k
          (i = i1) → irr q (k r) j)
        (ask q λ s → k (Rp q s r i))

    ~ans : ∀ q k r → k r ≡ ask q k
    ~ans q k r i =
      hcomp (λ j → λ where
          (i = i0) → irr q (k r) j
          (i = i1) → ask q k)
        (ask q λ s → k (Rp q r s i))

    ~ans-const : ∀ q t → t ≡ ask q (const t)
    ~ans-const q t i = hcomp (λ k → λ where
        (i = i0) → irr q t k
        (i = i1) → ask q (const t))
      (ask q (const t))

    ~ans-lemma : ∀ q t → PathP (λ i → t ≡ irr q t i) (~ans-const q t) refl
    ~ans-lemma q t j i = hcomp (λ k → λ where
        (i = i0) → irr q t k
        (i = i1) → irr q t (j ∧ k)
        (j = i1) → irr q t k)
      (ask q (const t))

    const-lemma₂ : ∀{q} k → const (ask q k) ≡ k
    const-lemma₂ {q = q} k = funExt (ans q k)

    null-iso : ∀ q → Iso (R q -> T) T
    null-iso q .fun = ask q
    null-iso q .inv = const
    null-iso q .rightInv = irr q
    null-iso q .leftInv = const-lemma₂

    null-path : ∀ q → (R q -> T) ≡ T
    null-path = isoToPath ∘ null-iso

  -- Being a sheaf is a property, at least for actual sheaves with
  -- propositional R q.
  isProp-isSheaf : isProp (isSheaf T)
  isProp-isSheaf s1 s2 = λ where i .ask q k → pre q k i ; i .irr q t → post q t i where
    open isSheaf
    pre : ∀ q k → s1 .ask q k ≡ s2 .ask q k
    pre q k i = hcomp (λ j → λ where
        (i = i0) → s1 .ask q λ r → s2 .irr q (k r) j
        (i = i1) → s1 .irr q (s2 .ask q k) j)
      (s1 .ask q λ r → s2 .ask q λ s → k (Rp q r s i))

    post : ∀ q t → PathP (λ i → pre q (const t) i ≡ t) (s1 .irr q t) (s2 .irr q t)
    post q t i j = hcomp (λ k → λ where
        (i = i0) → s1 .irr q (s2 .irr q t k) (j ∧ k)
        (i = i1) → s1 .irr q (s2 .irr q t (j ∧ k)) k
        (j = i1) → s1 .irr q (s2 .irr q t k) k)
      (s1 .ask q λ _ → s2 .ask q λ _ → t)

  isPropDep-isSheaf : isPropDep (isSheaf {ℓ = ℓ})
  isPropDep-isSheaf A = isOfHLevel→isOfHLevelDep 1 (λ _ → isProp-isSheaf) A

  -- Two sheaves are equal if their carrier type is equal.
  Sheaf≡ : ∀{A B : Sheaf ℓ} → A .fst ≡ B .fst -> A ≡ B
  Sheaf≡ {A = A} {B} P = ΣPathP (P , isPropDep-isSheaf (A .snd) (B .snd) P)

  -- Given a map from R q to sheaves, we can get a sheaf. This is
  -- actually an equivalence, with inverse const.
  absorb : ∀ q → (R q -> Sheaf ℓ) -> Sheaf ℓ
  absorb q K = λ where
    .fst → ∀ r → K r .fst
    .snd .isSheaf.ask q' k r → K r .snd .isSheaf.ask q' λ r' → k r' r
    .snd .isSheaf.irr q' f → funExt λ r → K r .snd .isSheaf.irr q' (f r)

  -- The type of sheaves form a sheaf via absorb. I imagine this makes them
  -- not strictly sheaves, but 'stacks' or what have you, due to univalence.
  -- I've heard that a known problem with (proper) sheaf models of type
  -- theory is that the collection of sheaves don't (in general) form a
  -- sheaf, leaving no way to interpret universes.
  isSheaf-Sheaf : isSheaf (Sheaf ℓ)
  isSheaf-Sheaf .isSheaf.ask = absorb
  isSheaf-Sheaf .isSheaf.irr q A = Sheaf≡ (null-path (A .snd) q)

module Alg (Q : Type) (R : Q -> Type) where
  open Base Q R
  open isSheaf

  -- This is the sheafification type. It is the free sheaf over A.
  data 𝒮 (A : Type ℓ) : Type ℓ where
    pur : A -> 𝒮 A
    que : (q : Q) -> (R q -> 𝒮 A) -> 𝒮 A
    con : ∀ q s → que q (const s) ≡ s

  -- Obviously the free sheaf is a sheaf.
  isSheaf-𝒮 : ∀(A : Type ℓ) → isSheaf (𝒮 A)
  isSheaf-𝒮 A .ask = que
  isSheaf-𝒮 A .irr = con

  record 𝒮-Motive ℓ' (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      Φ : 𝒮 A -> Type ℓ'
      on-pur : ∀ a → Φ (pur a)
      on-que : ∀ q k → (∀ r → Φ (k r)) -> Φ (que q k)
      on-con : ∀ q s → (Φs : Φ s)
             → PathP (λ i → Φ (con q s i)) (on-que q (const s) (const Φs)) Φs

  elim-𝒮 : (M : 𝒮-Motive ℓ T) -> ∀ s → M .𝒮-Motive.Φ s
  elim-𝒮 M = go where
    open 𝒮-Motive M
    go : ∀ s → Φ s
    go (pur x) = on-pur x
    go (que q k) = on-que q k (go ∘ k)
    go (con q s i) = on-con q s (go s) i

  -- This is the 'by-name' sheaf of natural numbers. The sheaf structure is
  -- added as constructors, so that the 'effects' can occur anywhere in the
  -- tree, rather than necessarily being lifted to the outside, which is
  -- what 𝒮 ℕ would be.
  data N : Type where
    zero : N
    suc : N -> N
    que : (q : Q) -> (R q -> N) -> N
    con : ∀ q n → que q (const n) ≡ n

  -- Π types of a family of sheaves form a sheaf.
  Π-shf : (∀ a → isSheaf (P a)) -> isSheaf (∀ a → P a)
  Π-shf sh .ask q k a = sh a .ask q λ r → k r a
  Π-shf sh .irr q f = funExt λ a → sh a .irr q (f a)

  -- Similar to the above N type, but for general well-founded trees.
  -- The sheaf structure looks almost identical to a well-founded tree,
  -- but it is subject to the quotient by 'purity.'
  data W₀ (A : Type ℓ) (B : A -> Type ℓ') : Type (ℓ-max ℓ ℓ') where
    sup : (x : A) -> (B x -> W₀ A B) -> W₀ A B
    que : (q : Q) -> (R q -> W₀ A B) -> W₀ A B
    con : ∀ q x -> que q (const x) ≡ x

  W₀-shf : ∀(A : Type ℓ) (B : A -> Type ℓ') → isSheaf (W₀ A B)
  W₀-shf A B .isSheaf.ask = que
  W₀-shf A B .isSheaf.irr = con

  -- Paths in a sheaf are sheaves.
  PP-shf : ∀{A : I -> Type ℓ} x y
         → (∀ i → isSheaf (A i)) -> isSheaf (PathP A x y)
  PP-shf x y Ash = λ where
    .ask q k i → hcomp (λ k → λ where
        (i = i0) → Ash i0 .irr q x k
        (i = i1) → Ash i1 .irr q y k)
      (Ash i .ask q λ r → k r i)
    .irr q p j i → hcomp (λ k → λ where
        (i = i0) → Ash i0 .irr q x k
        (i = i1) → Ash i1 .irr q y k
        (j = i1) → Ash i .irr q (p i) k)
      (Ash i .ask q (λ _ → p i))

  data ∥_∥₁ (A : Type ℓ) : Type ℓ where
    ∣_∣₁ : A -> ∥ A ∥₁
    squash₁ : isProp ∥ A ∥₁
    que : (q : Q) -> (R q -> ∥ A ∥₁) -> ∥ A ∥₁
    con : ∀ q x -> que q (const x) ≡ x

module Uni {Q : Type} {R : Q -> Type} (Rp : ∀ q → isProp (R q)) where
  open Base Q R
  open Alg Q R
  open isSheaf

  -- The universe is interpreted by the type of sheaves of a
  -- corresponding size.
  𝒰 : (ℓ : Level) -> Sheaf (ℓ-suc ℓ)
  𝒰 ℓ .fst = Sheaf ℓ
  𝒰 ℓ .snd = Lemmas.isSheaf-Sheaf Rp

  𝒰₀ = 𝒰 ℓ-zero

  -- More universe-like convenience functions for accessing the parts of
  -- a universe value.
  El : ⟨ 𝒰 ℓ ⟩ -> Type ℓ
  El A = A .fst

  isSheaf-El : (A : ⟨ 𝒰 ℓ ⟩) -> isSheaf (El A)
  isSheaf-El A = A .snd

  Σ : (A : ⟨ 𝒰 ℓ ⟩) -> (B : El A -> ⟨ 𝒰 ℓ' ⟩) -> ⟨ 𝒰 (ℓ-max ℓ ℓ') ⟩
  Σ A B = λ where
    .fst → 𝒮 (Σ[ x ∈ El A ] El (B x))
    .snd → isSheaf-𝒮 _

  Π : (A : ⟨ 𝒰 ℓ ⟩) -> (B : El A -> ⟨ 𝒰 ℓ' ⟩) -> ⟨ 𝒰 (ℓ-max ℓ ℓ') ⟩
  Π A B = λ where
    .fst → (x : El A) → El (B x)
    .snd → Π-shf (λ x → isSheaf-El (B x))

  W : (A : ⟨ 𝒰 ℓ ⟩) -> (B : El A -> ⟨ 𝒰 ℓ' ⟩) -> ⟨ 𝒰 (ℓ-max ℓ ℓ') ⟩
  W A B = λ where
    .fst → W₀ (El A) (El ∘ B)
    .snd → W₀-shf (El A) (El ∘ B)

  PP : ∀(A : I -> ⟨ 𝒰 ℓ ⟩) (x : El (A i0)) (y : El (A i1)) -> ⟨ 𝒰 ℓ ⟩
  PP A x y = λ where
    .fst → PathP (λ i → El (A i)) x y
    .snd → PP-shf x y (λ i → isSheaf-El (A i))

  ℕ : ⟨ 𝒰₀ ⟩
  ℕ .fst = N
  ℕ .snd .ask = que
  ℕ .snd .irr = con

  -- Inductive types share behavior for the freely added sheaf
  -- constructors, so it can be factored out into these two cases.
  on-ask : (P : T -> ⟨ 𝒰 ℓ ⟩)
         → (Tsh : isSheaf T)
         → (q : Q) -> (k : R q -> T)
         → (∀ r -> El (P (k r)))
         → El (P (Tsh .ask q k))
  on-ask P Tsh q k K =
    P (Tsh .ask q k) .snd .ask q λ r →
      transport (λ i → El (P (Lemmas.~ans Rp Tsh q k r i))) (K r)

  on-irr : (P : T -> ⟨ 𝒰 ℓ ⟩)
         → (Tsh : isSheaf T)
         → (q : Q) -> (t : T) -> (Pt : El (P t))
         → PathP (λ i → El (P (Tsh .irr q t i)))
             (on-ask P Tsh q (const t) (const Pt))
             Pt
  on-irr P Tsh q t Pt i = P (Tsh .irr q t i) .snd .irr q
    (transp (λ j → P (Lemmas.~ans-lemma Rp Tsh q t i j) .fst) i Pt) i

  ℕ-elim : {P : El ℕ -> ⟨ 𝒰 ℓ ⟩}
         → ⟨ P zero ⟩
         → (∀ n → ⟨ P n ⟩ -> ⟨ P (suc n) ⟩)
         → ∀ n → ⟨ P n ⟩
  ℕ-elim {ℓ} {P} Pz Ps = go where
    go : ∀ n → ⟨ P n ⟩
    go zero = Pz
    go (suc n) = Ps n (go n)
    go (que q k) = on-ask P (snd ℕ) q k (go ∘ k)
    go (con q n i) = on-irr P (snd ℕ) q n (go n) i

  W-elim : {A : ⟨ 𝒰 ℓ ⟩} {B : El A -> ⟨ 𝒰 ℓ' ⟩} {P : El (W A B) -> ⟨ 𝒰 ℓ ⟩}
         → (∀ a f → (∀ b → El (P (f b))) → El (P (sup a f)))
         → ∀ x -> ⟨ P x ⟩
  W-elim {A = A} {B} {P} h = go where
    go : ∀ x → ⟨ P x ⟩
    go (sup x f) = h x f (go ∘ f)
    go (que q k) = on-ask P (W A B .snd) q k (go ∘ k)
    go (con q x i) = on-irr P (W A B .snd) q x (go x) i

  IsProp : ⟨ 𝒰 ℓ ⟩ -> ⟨ 𝒰 ℓ ⟩
  IsProp A = Π A λ x → Π A λ y → PP (λ _ → A) x y

  ∥_∥ : ⟨ 𝒰 ℓ ⟩ -> ⟨ 𝒰 ℓ ⟩
  ∥ A ∥ .fst = ∥ El A ∥₁
  ∥ A ∥ .snd .isSheaf.ask = que
  ∥ A ∥ .snd .isSheaf.irr = con

  ∥∥-elim : ∀{A : ⟨ 𝒰 ℓ ⟩} {P : El ∥ A ∥ -> ⟨ 𝒰 ℓ' ⟩}
          → El (Π ∥ A ∥ λ x → IsProp (P x))
          → (∀ x → El (P ∣ x ∣₁))
          → ∀ x → El (P x)
  ∥∥-elim {A = A} {P} Pp b = go where
    go : ∀ x → _
    go ∣ x ∣₁ = b x
    go (squash₁ x y i) =
      isOfHLevel→isOfHLevelDep 1 Pp (go x) (go y) (squash₁ x y) i
    go (que q k) = on-ask P (∥ A ∥ .snd) q k (go ∘ k)
    go (con q x i) = on-irr P (∥ A ∥ .snd) q x (go x) i
