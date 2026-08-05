{-# OPTIONS --postfix-projections --without-K #-}

-- Original paper:
--   https://jashug.github.io/papers/whynotw.pdf

-- This module performs a case of the construction starting from
-- indexed W-types, indicating that the challenging aspect of
-- encoding nested/indexed inductive types in an intensional theory
-- is getting the encoding of indexing to work out.

module WhyNotW where
open import Level
open import Function

open import Data.Bool as Bool
open import Data.Empty as Empty
open import Data.Product as Prod
open import Data.Unit as Unit

open import Relation.Binary.PropositionalEquality

variable
  ℓ : Level

-- Attempting to encode this Tree type, which is itself an indexed
-- encoding of:
--
--   data Tree : Set where
--     leaf : Tree
--     wide : List Tree → Tree
module Ind where
  data Tree : Bool → Set where
    leaf : Tree false
    wide : Tree true → Tree false
    nil : Tree true
    cons : Tree false → Tree true → Tree true

  rec₀
    : (P : ∀ b → Tree b → Set)
    → P false leaf
    → (∀ t → P true t → P false (wide t))
    → P true nil
    → (∀ t l → P false t → P true l → P true (cons t l))
    →  ∀{b} t → P b t
  rec₀ P pl pw pn pc leaf = pl
  rec₀ P pl pw pn pc (wide t) = pw t (rec₀ P pl pw pn pc t)
  rec₀ P pl pw pn pc nil = pn
  rec₀ P pl pw pn pc (cons t l) = pc t l (rec₀ P pl pw pn pc t) (rec₀ P pl pw pn pc l)

-- The slice of Set over a given set. Another view of I → Set.
Set/ : Set → Set₁
Set/ I = Σ[ T ∈ Set ] (T → I)

_⟩_ : ∀{I} → (T : Set/ I) → T .proj₁ → I
(_ , f) ⟩ x = f x

-- Indexed W-types
module Indexed (I : Set) where
  private
    variable
      A : I → Set
      B : ∀ i → A i → Set/ I

  data IW (A : I → Set) (B : ∀ i → A i → Set/ I) : I → Set where
    sup : (i : I) → (x : A i) → (f : ∀ y → IW A B (B i x ⟩ y)) → IW A B i

  wrec : ∀{ℓ} (P : ∀ i → IW A B i → Set ℓ)
      → (∀ i x f → (∀ y → P _ (f y)) → P i (sup i x f))
      → ∀{i} w → P i w
  wrec P g (sup i x f) = g i x f (wrec P g ∘ f)

-- Non-indexed W-types
data W (A : Set) (B : A → Set) : Set where
  sup : (x : A) → (f : B x → W A B) → W A B

-- Building indexed W-types from non-indexed ones.
module MkInd (I : Set) where

  variable
    A : I → Set
    B : ∀ i → A i → Set/ I

  PW : (A : I → Set) → (B : ∀ i → A i → Set/ I) → Set
  PW A B = W (Σ I A) (proj₁ ∘ uncurry B)

  canonical : PW A B → I → Set
  canonical {B = B} (sup (i₀ , x) f) i₁
    = (i₀ ≡ i₁)
    × (∀ y → canonical {B = B} (f y) (B i₀ x ⟩ y))

  EW : (A : I → Set) → (B : ∀ i → A i → Set/ I) → I → Set
  EW A B i = Σ[ w ∈ PW A B ] canonical {B = B} w i

  zup : (i : I) → (x : A i) → (f : ∀ y → EW A B (B i x ⟩ y)) → EW A B i
  zup i x f = sup (i , x) (proj₁ ∘ f) , refl , (proj₂ ∘ f)

  ewrec
    : (P : ∀ i → EW A B i → Set ℓ)
    → (∀ i x f → (∀ y → P _ (f y)) → P i (zup i x f))
    → ∀{i} w → P i w
  ewrec P g (sup (i , x) f , e , subcanon)
    = J Q e (g i x (λ y → f y , subcanon y) λ y → ewrec P g (f y , subcanon y))
    where
    Q : (i : I) → _ ≡ i → Set _
    Q i e =
      P i (sup (_ , x) f , e , subcanon)

  lemma
    : (P : ∀ i → EW A B i → Set)
    → (g : ∀ i x f → (∀ y → P _ (f y)) → P i (zup i x f))
    → ∀ i x f
    → ewrec P g (zup i x f) ≡ g i x f λ y → ewrec P g (f y)
  lemma P g i x f = refl

-- The container for the indexed inductive type above.
module Container where
  data TC : Bool → Set where
    lf wi : TC false
    nl cn : TC true

  TB : ∀ i → TC i → Set/ Bool
  TB _ lf = ⊥ , ⊥-elim
  TB _ wi = ⊤ , λ _ → true
  TB _ nl = ⊥ , ⊥-elim
  TB _ cn = Bool , λ{ false → false ; true → true }

-- Encoding the inductive type using the directly defined
-- indexed inductive types. Some things are a bit nicer due
-- to pattern matching.
module IxEnc where
  open Indexed Bool using (IW; sup)
  open Indexed hiding (IW; sup)
  open Container

  TT : Bool → Set
  TT = IW TC TB

  pre-leaf₀ : (b : ⊥) → IW TC TB (TB false lf ⟩ b)
  pre-leaf₀ ()

  leaf₀ : TT false
  leaf₀ = sup false lf pre-leaf₀

  wide₀ : TT true → TT false
  wide₀ sub = sup false wi λ _ → sub

  pre-nil₀ : (b : ⊥) → IW TC TB (TB true nl ⟩ b)
  pre-nil₀ ()

  nil₀ : TT true
  nil₀ = sup true nl pre-nil₀

  pre-cons₀ : TT false → TT true → (b : Bool) → IW TC TB (TB true cn ⟩ b)
  pre-cons₀ x xs false = x
  pre-cons₀ x xs  true = xs

  cons₀ : TT false → TT true → TT true
  cons₀ x xs = sup true cn (pre-cons₀ x xs)

  canonical : ∀{b} → TT b → Set
  canonical (sup _ lf f) = pre-leaf₀ ≡ f
  canonical (sup _ wi f) = canonical (f tt)
  canonical (sup _ nl f) = pre-nil₀ ≡ f
  canonical (sup _ cn f)
    = canonical (f false) × canonical (f true)
    × Σ[ x ∈ _ ] Σ[ xs ∈ _ ] pre-cons₀ x xs ≡ f

  Tree : Bool → Set
  Tree b = Σ (TT b) canonical

  leaf : Tree false
  leaf = leaf₀ , refl

  wide : Tree true → Tree false
  wide sub = wide₀ (proj₁ sub) , proj₂ sub

  nil : Tree true
  nil = nil₀ , refl

  cons : Tree false → Tree true → Tree true
  cons x xs .proj₁ = cons₀ (proj₁ x) (proj₁ xs)
  cons x xs .proj₂ = proj₂ x , proj₂ xs , proj₁ x , proj₁ xs , refl

  rec
    : (P : ∀ b → Tree b → Set)
    → P false leaf
    → (∀ t → P true t → P false (wide t))
    → P true nil
    → (∀ t l → P false t → P true l → P true (cons t l))
    →  ∀{b} t → P b t

  rec P pl pw pn pc = go
    where
    go : ∀{b} t → P b t
    go (sup _ lf f , canon)
      = J (λ f e → P _ (sup _ lf f , e)) canon pl

    go (sup _ wi f , canon)
      = pw (f tt , canon) (go (f tt , canon))

    go (sup _ nl f , canon)
      = J (λ f e → P _ (sup _ nl f , e)) canon pn

    go (sup _ cn f , cx , cxs , x , xs , ceq)
      = J Q ceq pc' cx cxs (go (f false , cx)) (go (f true , cxs))
      where
      Q : (g : (b : Bool) → IW TC TB (TB true cn ⟩ b))
        → pre-cons₀ x xs ≡ g
        → Set
      Q g e = (cy : canonical (g false))
            → (cys : canonical (g true))
            → P _ (g false , cy)
            → P _ (g  true , cys)
            → P _ (sup _ cn g , cy , cys , x , xs , e)

      pc' : Q (pre-cons₀ x xs) refl
      pc' cx cxs px pxs = pc (x , cx) (xs , cxs) px pxs

  comp₀ : ∀ P pl pw pn pc → rec P pl pw pn pc leaf ≡ pl
  comp₀ _ _ _ _ _ = refl

  comp₁ : ∀ P pl pw pn pc l → rec P pl pw pn pc (wide l) ≡ pw l (rec P pl pw pn pc l)
  comp₁ _ _ _ _ _ _ = refl

  comp₂ : ∀ P pl pw pn pc → rec P pl pw pn pc nil ≡ pn
  comp₂ _ _ _ _ _ = refl

  comp₃ : ∀ P pl pw pn pc x xs
    → rec P pl pw pn pc (cons x xs)
    ≡ pc x xs (rec P pl pw pn pc x) (rec P pl pw pn pc xs)
  comp₃ _ _ _ _ _ _ _ = refl

-- Fully encoding the indexed type into W-types + the identity type,
-- by combining the stages.
module FullEnc where
  open MkInd Bool using (zup) renaming (EW to IW; ewrec to rec)
  open MkInd hiding (EW; zup; canonical; ewrec)
  open Container

  TT : Bool → Set
  TT = IW TC TB

  pre-leaf₀ : (b : ⊥) → IW TC TB (TB false lf ⟩ b)
  pre-leaf₀ ()

  leaf₀ : TT false
  leaf₀ = zup false lf pre-leaf₀

  wide₀ : TT true → TT false
  wide₀ sub = zup false wi λ _ → sub

  pre-nil₀ : (b : ⊥) → IW TC TB (TB true nl ⟩ b)
  pre-nil₀ ()

  nil₀ : TT true
  nil₀ = zup true nl pre-nil₀

  pre-cons₀ : TT false → TT true → (b : Bool) → IW TC TB (TB true cn ⟩ b)
  pre-cons₀ x xs false = x
  pre-cons₀ x xs  true = xs

  cons₀ : TT false → TT true → TT true
  cons₀ x xs = zup true cn (pre-cons₀ x xs)

  canonical : ∀{b} → TT b → Set
  canonical w = rec (λ _ _ → Set) cases w 
    where
    cases : _
    cases _ lf f _ = pre-leaf₀ ≡ f
    cases _ wi f C = C tt
    cases _ nl f _ = pre-nil₀ ≡ f
    cases _ cn f C =
      C false × C true × Σ[ x ∈ _ ] Σ[ xs ∈ _ ] pre-cons₀ x xs ≡ f

  Tree : Bool → Set
  Tree b = Σ (TT b) canonical

  leaf : Tree false
  leaf = leaf₀ , refl

  wide : Tree true → Tree false
  wide sub = wide₀ (proj₁ sub) , proj₂ sub

  nil : Tree true
  nil = nil₀ , refl

  cons : Tree false → Tree true → Tree true
  cons x xs .proj₁ = cons₀ (proj₁ x) (proj₁ xs)
  cons x xs .proj₂ = proj₂ x , proj₂ xs , proj₁ x , proj₁ xs , refl

  trec
    : (P : ∀ b → Tree b → Set)
    → P false leaf
    → (∀ t → P true t → P false (wide t))
    → P true nil
    → (∀ t l → P false t → P true l → P true (cons t l))
    →  ∀{b} t → P b t
  trec P pl pw pn pc (rep , canon)
    = rec (λ i w → (c : canonical w) → P i (w , c)) cases rep canon
    where
    cases : _
    cases _ lf f _ canon
      = J (λ f e → P _ (zup _ lf f , e)) canon pl

    cases _ wi f rec canon
      = pw (f tt , canon) (rec tt canon)

    cases _ nl f _ canon
      = J (λ f e → P _ (zup _ nl f , e)) canon pn

    cases _ cn f rec (cx , cxs , x , xs , ceq)
      = J Q ceq pc' cx cxs (rec false cx) (rec true cxs)
      where
      Q : (g : (b : Bool) → IW TC TB (TB true cn ⟩ b))
        → pre-cons₀ x xs ≡ g
        → Set
      Q g e = (cy : canonical (g false))
            → (cys : canonical (g true))
            → P _ (g false , cy)
            → P _ (g  true , cys)
            → P _ (zup _ cn g , cy , cys , x , xs , e)

      pc' : Q (pre-cons₀ x xs) refl
      pc' cx cxs px pxs = pc (x , cx) (xs , cxs) px pxs

  -- Computation rules are still judgmental.
  comp₀ : ∀ P pl pw pn pc → trec P pl pw pn pc leaf ≡ pl
  comp₀ _ _ _ _ _ = refl

  comp₁ : ∀ P pl pw pn pc l → trec P pl pw pn pc (wide l) ≡ pw l (trec P pl pw pn pc l)
  comp₁ _ _ _ _ _ _ = refl

  comp₂ : ∀ P pl pw pn pc → trec P pl pw pn pc nil ≡ pn
  comp₂ _ _ _ _ _ = refl

  comp₃ : ∀ P pl pw pn pc x xs
    → trec P pl pw pn pc (cons x xs)
    ≡ pc x xs (trec P pl pw pn pc x) (trec P pl pw pn pc xs)
  comp₃ _ _ _ _ _ _ _ = refl

