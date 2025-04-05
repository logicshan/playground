{-# OPTIONS --cubical --rewriting #-}

--module DeMorgan where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_; comp)
open import Agda.Primitive
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Nat using (ℕ)
open import Function renaming (id to id')
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.HLevels using (isSet→)
open import Cubical.Data.Fin.Properties using (isSetFin)
-- open import Cubical.Categories.Instances.Sets

variable
  ℓ ℓ' : Level
  A B C : Set ℓ

{-# BUILTIN REWRITE _≡_ #-}

data FreeDM (A : Set lzero) : Set lzero where
  var   : A → FreeDM A
  𝟎     : FreeDM A
  𝟏     : FreeDM A
  _∧_   : FreeDM A → FreeDM A → FreeDM A
  _∨_   : FreeDM A → FreeDM A → FreeDM A
  ¬_    : FreeDM A → FreeDM A

  -- Lattice laws as paths
  ∧-comm    : ∀ x y → x ∧ y ≡ y ∧ x
  ∧-assoc   : ∀ x y z → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
  ∨-comm    : ∀ x y → x ∨ y ≡ y ∨ x
  ∨-assoc   : ∀ x y z → x ∨ (y ∨ z) ≡ (x ∨ y) ∨ z
  ∧-absorb  : ∀ x y → x ∧ (x ∨ y) ≡ x
  ∨-absorb  : ∀ x y → x ∨ (x ∧ y) ≡ x

  -- Bounded lattice laws
  ∧-identity : ∀ x → (x ∧ 𝟏) ≡ x
  ∨-identity : ∀ x → (x ∨ 𝟎) ≡ x

  -- De Morgan laws
  involution : ∀ x → (¬ (¬ x)) ≡ x
  deMorgan-∧ : ∀ x y → ¬ (x ∧ y) ≡ (¬ x) ∨ (¬ y)
  deMorgan-∨ : ∀ x y → ¬ (x ∨ y) ≡ (¬ x) ∧ (¬ y)

  squash : (x y : FreeDM A) → (p q : x ≡ y) → p ≡ q

module _ where
  open Category

  FinSet : Category lzero lzero
  ob FinSet = ℕ
  Hom[_,_] FinSet n m = Fin n → Fin m
  id FinSet = id'
  _⋆_ FinSet f g = λ x → g (f x)
  ⋆IdL FinSet f = funExt λ x i → f x
  ⋆IdR FinSet f = funExt λ x i → f x
  ⋆Assoc FinSet f g h = λ i x → h (g (f x))
  isSetHom FinSet = isSet→ isSetFin
{-
module _ where
  open Category
  open Functor

  SET : Category (lsuc lzero) lzero
  ob SET = Set
  Hom[_,_] SET S T = S → T
  id SET = λ z → z
  _⋆_ SET = λ f g z₁ → g (f z₁)
  ⋆IdL SET f = funExt λ x i → f x
  ⋆IdR SET f = funExt (λ x₁ i → f x₁)
  ⋆Assoc SET f g h = λ i x → h (g (f x))
  isSetHom SET = {!!}
-}

module _ where
  open Category
  open Functor

  SET : Category (lsuc lzero) lzero
  ob SET = Σ[ S ∈ Set ] (isSet S)
  Hom[_,_] SET (S , _) (T , _) = S → T
  id SET = λ z → z
  _⋆_ SET = λ f g z₁ → g (f z₁)
  ⋆IdL SET f = funExt λ x i → f x
  ⋆IdR SET f = funExt (λ x₁ i → f x₁)
  ⋆Assoc SET f g h = λ i x → h (g (f x))
  isSetHom SET {x} {y} = isSet→ (snd y)



  DM : Functor SET SET

  postulate
    fst-axiom : ∀ {x : Σ[ S ∈ Set ] (isSet S)} → fst (F-ob DM x) ≡ FreeDM (fst x)
--    {-# REWRITE fst-axiom #-}

{-
  postulate
    fst-axiom : ∀ {S} → fst (F-ob DM (S , _)) ≡ FreeDM S
    {-# REWRITE fst-axiom #-}
-}

  F-ob DM (S , isSetS) = (FreeDM S) , squash
  F-hom DM f (var x) = var (f x)
  F-hom DM f 𝟎 = 𝟎
  F-hom DM f 𝟏 = 𝟏
  F-hom DM f (S ∧ S₁) = (F-hom DM f S) ∧ (F-hom DM f S₁)
--  F-hom DM f (S ∧ S₁) = (F-hom DM f (subst id' (sym fst-axiom) S)) ∧ (F-hom DM f ((subst id' (sym fst-axiom) S₁)))
{-    where
    lemma : {x : Σ Set _} → fst (F-ob DM (fst x , _)) ≡ FreeDM (fst x)
    lemma {S , y} = {!!} -}
--  F-hom DM f (S ∨ S₁) rewrite fst-axiom {_ , _} = {!!}
  F-hom DM f (S ∨ S₁) = {!_∨_!}
  F-hom DM f (¬ S) = {!!}
  F-hom DM f (∧-comm S S₁ i) = {!!}
  F-hom DM f (∧-assoc S S₁ S₂ i) = {!!}
  F-hom DM f (∨-comm S S₁ i)     = {!!}
  F-hom DM f (∨-assoc S S₁ S₂ i) = {!!}
  F-hom DM f (∧-absorb S S₁ i)   = {!!}
  F-hom DM f (∨-absorb S S₁ i)   = {!!}
  F-hom DM f (∧-identity S i)    = {!!}
  F-hom DM f (∨-identity S i)    = {!!}
  F-hom DM f (involution S i)    = {!!}
  F-hom DM f (deMorgan-∧ S S₁ i) = {!!}
  F-hom DM f (deMorgan-∨ S S₁ i) = {!!}
{-
  F-hom DM f (∨-comm S S₁ i) = {!!}
  F-hom DM f (∨-assoc S S₁ S₂ i) = {!!}
  F-hom DM f (∧-absorb S S₁ i) = {!!}
  F-hom DM f (∨-absorb S S₁ i) = {!!}
  F-hom DM f (∧-identity S i) = {!!}
  F-hom DM f (∨-identity S i) = {!!}
  F-hom DM f (involution S i) = {!!}
  F-hom DM f (deMorgan-∧ S S₁ i) = {!!}
  F-hom DM f (deMorgan-∨ S S₁ i) = {!!}
-}
  F-hom DM f (squash S S₁ p q i i₁) = {!!}
  F-id DM = {!!}
  F-seq DM = {!!}
