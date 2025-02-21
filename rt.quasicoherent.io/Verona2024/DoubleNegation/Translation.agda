{-# OPTIONS --cubical-compatible -WnoUnsupportedIndexedMatch --allow-unsolved-metas #-}
module Verona2024.DoubleNegation.Translation where

open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit renaming (⊤ to Unit)
open import Data.List
open import Relation.Binary.PropositionalEquality

withType : (A : Set) → A → A
withType _ x = x

data _∈_ {A : Set} : A → List A → Set where
  here  : {x : A}   {ys : List A} → x ∈ (x ∷ ys)
  there : {x y : A} {ys : List A} → x ∈ ys → x ∈ (y ∷ ys)

∈-++ : {A : Set} {xs ys : List A} {z : A} → z ∈ xs → z ∈ (xs ++ ys)
∈-++ here = here
∈-++ (there i) = there (∈-++ i)

data Vector {A : Set} (F : A → Set) : List A → Set where
  []  : Vector F []
  _∷_ : {x : A} {xs : List A} → F x → Vector F xs → Vector F (x ∷ xs)

lookupV : {A : Set} {F : A → Set} {a : A} {as : List A} → Vector F as → a ∈ as → F a
lookupV (x ∷ env) here      = x
lookupV (x ∷ env) (there v) = lookupV env v

mapV : {A : Set} {F G : A → Set} {as : List A} → ({a : A} → F a → G a) → Vector F as → Vector G as
mapV f []       = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

record Signature : Set₁ where
  field
    Ty  : Set
    Fun : Set
    Rel : Set

    dom : Fun → List Ty
    cod : Fun → Ty

    fld : Rel → List Ty

module Logic (Σ : Signature) where
  open Signature Σ

  Cxt : Set
  Cxt = List Ty

  data Term (Γ : Cxt) : Ty → Set where
    var : {ty : Ty} → ty ∈ Γ → Term Γ ty
    _$_ : (f : Fun) → Vector (Term Γ) (dom f) → Term Γ (cod f)

  data Frag : Set where
    coh 1st : Frag

  data Form : Cxt → Frag → Set where
    _≈_ : {frag : Frag} {Γ : Cxt} {ty : Ty} → Term Γ ty → Term Γ ty → Form Γ frag
    at  : {frag : Frag} {Γ : Cxt} → (r : Rel) → Vector (Term Γ) (fld r) → Form Γ frag
    ⊤   : {frag : Frag} {Γ : Cxt} → Form Γ frag
    ⊥   : {frag : Frag} {Γ : Cxt} → Form Γ frag
    _∧_ : {frag : Frag} {Γ : Cxt} → Form Γ frag → Form Γ frag → Form Γ frag
    _∨_ : {frag : Frag} {Γ : Cxt} → Form Γ frag → Form Γ frag → Form Γ frag
    _⇒_ : {Γ : Cxt} → Form Γ 1st → Form Γ 1st → Form Γ 1st
    FA  : {Γ : Cxt} {ty : Ty} → Form (ty ∷ Γ) 1st → Form Γ 1st
    EX  : {frag : Frag} {Γ : Cxt} {ty : Ty} → Form (ty ∷ Γ) frag → Form Γ frag

  {-# TERMINATING #-}
  raise : {Γ : Cxt} {σ τ : Ty} → Term Γ τ → Term (σ ∷ Γ) τ
  raise (var i)  = var (there i)
  raise (f $ xs) = f $ mapV raise xs

  shift : {τ : Ty} {Γ Δ : Cxt} → ({σ : Ty} → σ ∈ Γ → Term Δ σ) → ({σ : Ty} → σ ∈ (τ ∷ Γ) → Term (τ ∷ Δ) σ)
  shift π here      = var here
  shift π (there i) = raise (π i)

  {-# TERMINATING #-}
  subs₀ : {Γ Δ : Cxt} {τ : Ty} → ({σ : Ty} → σ ∈ Γ → Term Δ σ) → Term Γ τ → Term Δ τ
  subs₀ π (var i)  = π i
  subs₀ π (f $ xs) = f $ mapV (subs₀ π) xs

  subs : {frag : Frag} {Γ Δ : Cxt} → ({σ : Ty} → σ ∈ Γ → Term Δ σ) → Form Γ frag → Form Δ frag
  subs π ⊤         = ⊤
  subs π ⊥         = ⊥
  subs π (φ ∧ ψ)   = subs π φ ∧ subs π ψ
  subs π (φ ∨ ψ)   = subs π φ ∨ subs π ψ
  subs π (φ ⇒ ψ)   = subs π φ ⇒ subs π ψ
  subs π (FA φ)    = FA (subs (shift π) φ)
  subs π (EX φ)    = EX (subs (shift π) φ)
  subs π (s ≈ t)   = subs₀ π s ≈ subs₀ π t
  subs π (at r xs) = at r (mapV (subs₀ π) xs)

  inj : {Γ : Cxt} {τ : Ty} → ({σ : Ty} → σ ∈ Γ → Term (τ ∷ Γ) σ)
  inj i = var (there i)

  weaken : {ty : Ty} {Γ : Cxt} {frag : Frag} → Form Γ frag → Form (ty ∷ Γ) frag
  weaken = subs inj

  inj-++ : {Γ Δ : Cxt} → ({σ : Ty} → σ ∈ Γ → Term (Γ ++ Δ) σ)
  inj-++ i = var (∈-++ i)

  weaken-++ : {Γ Δ : Cxt} {frag : Frag} → Form Γ frag → Form (Γ ++ Δ) frag
  weaken-++ {Γ} {Δ} = subs (inj-++ {Γ} {Δ})

  relax : {Γ : Cxt} → Form Γ coh → Form Γ 1st
  relax (s ≈ t)   = s ≈ t
  relax (at r xs) = at r xs
  relax ⊤         = ⊤
  relax ⊥         = ⊥
  relax (φ ∧ ψ)   = relax φ ∧ relax ψ
  relax (φ ∨ ψ)   = relax φ ∨ relax ψ
  relax (EX φ)    = EX (relax φ)

  data Mode : Set where
    min int class : Mode

  _≥_ : Mode → Mode → Set
  min   ≥ min = Unit
  int   ≥ min = Unit
  int   ≥ int = Unit
  class ≥ _   = Unit
  _     ≥ _   = Empty

  Axioms : Set₁
  Axioms = {Γ : Cxt} → (α β : Form Γ 1st) → Set

  join-variables : {Γ : Cxt} {τ : Ty} → {σ : Ty} → σ ∈ (τ ∷ τ ∷ Γ) → Term (τ ∷ τ ∷ Γ) σ
  join-variables here              = var (there here)
  join-variables (there here)      = var (there here)
  join-variables (there (there i)) = var (there (there i))

  module Proof (mode : Mode) (ax : Axioms) where
    data _⊢_ : {Γ : Cxt} → Form Γ 1st → Form Γ 1st → Set where
      axiom        : {Γ : Cxt} {α β : Form Γ 1st} → ax α β → α ⊢ β
      identity     : {Γ : Cxt} {φ : Form Γ 1st} → φ ⊢ φ
      substitution : {Γ Δ : Cxt} {α β : Form Γ 1st} (π : {σ : Ty} → σ ∈ Γ → Term Δ σ) → α ⊢ β → subs π α ⊢ subs π β
      cut          : {Γ : Cxt} {α β γ : Form Γ 1st} → α ⊢ β → β ⊢ γ → α ⊢ γ
      eq-refl      : {τ : Ty} → (withType (Form (τ ∷ []) 1st) ⊤) ⊢ (var here ≈ var here)
      eq-subst     : {Γ : Cxt} {τ : Ty} {α : Form (τ ∷ τ ∷ Γ) 1st} → ((var here ≈ var (there here)) ∧ α) ⊢ subs join-variables α  -- enough?
      top-intr     : {Γ : Cxt} {α : Form Γ 1st} → α ⊢ ⊤
      conj-elimₗ   : {Γ : Cxt} {α β : Form Γ 1st} → (α ∧ β) ⊢ α
      conj-elimᵣ   : {Γ : Cxt} {α β : Form Γ 1st} → (α ∧ β) ⊢ β
      conj-intr    : {Γ : Cxt} {α β χ : Form Γ 1st} → χ ⊢ α → χ ⊢ β → χ ⊢ (α ∧ β)
      bot-elim     : {_ : mode ≥ int} {Γ : Cxt} {α : Form Γ 1st} → ⊥ ⊢ α
      disj-intrₗ   : {Γ : Cxt} {α β : Form Γ 1st} → α ⊢ (α ∨ β)
      disj-intrᵣ   : {Γ : Cxt} {α β : Form Γ 1st} → β ⊢ (α ∨ β)
      disj-elim    : {Γ : Cxt} {α β χ : Form Γ 1st} → α ⊢ χ → β ⊢ χ → (α ∨ β) ⊢ χ
      impl₁        : {Γ : Cxt} {α β χ : Form Γ 1st} → (α ∧ β) ⊢ χ → α ⊢ (β ⇒ χ)
      impl₂        : {Γ : Cxt} {α β χ : Form Γ 1st} → α ⊢ (β ⇒ χ) → (α ∧ β) ⊢ χ
      forall₁      : {Γ : Cxt} {ty : Ty} {α : Form Γ 1st} {β : Form (ty ∷ Γ) 1st} → weaken α ⊢ β → α ⊢ FA β
      forall₂      : {Γ : Cxt} {ty : Ty} {α : Form Γ 1st} {β : Form (ty ∷ Γ) 1st} → α ⊢ FA β → weaken α ⊢ β
      exists₁      : {Γ : Cxt} {ty : Ty} {α : Form (ty ∷ Γ) 1st} {β : Form Γ 1st} → α ⊢ weaken β → EX α ⊢ β
      exists₂      : {Γ : Cxt} {ty : Ty} {α : Form (ty ∷ Γ) 1st} {β : Form Γ 1st} → EX α ⊢ β → α ⊢ weaken β
      lem          : {_ : mode ≥ class} {Γ : Cxt} {α : Form Γ 1st} → ⊤ ⊢ (α ∨ (α ⇒ ⊥))

    ∧-comm : {Γ : Cxt} {α β : Form Γ 1st} → (α ∧ β) ⊢ (β ∧ α)
    ∧-comm = conj-intr conj-elimᵣ conj-elimₗ

    return : {Γ : Cxt} {φ χ : Form Γ 1st} → φ ⊢ ((φ ⇒ χ) ⇒ χ)
    return = {!!}

    contrapositive : {Γ : Cxt} {α β χ : Form Γ 1st} → α ⊢ β → (β ⇒ χ) ⊢ (α ⇒ χ)
    contrapositive p = {!!}

    escape : {Γ : Cxt} {γ : Form Γ 1st} → ((γ ⇒ γ) ⇒ γ) ⊢ γ
    escape = {!!}

    ¬-stable : {Γ : Cxt} {φ χ : Form Γ 1st} → (((φ ⇒ χ) ⇒ χ) ⇒ χ) ⊢ (φ ⇒ χ)
    ¬-stable = contrapositive return

    ¬¬-monotone : {Γ : Cxt} {α β χ : Form Γ 1st} → α ⊢ β → ((α ⇒ χ) ⇒ χ) ⊢ ((β ⇒ χ) ⇒ χ)
    ¬¬-monotone p = contrapositive (contrapositive p)

    ¬¬-conj : {Γ : Cxt} {α β χ : Form Γ 1st} → (((α ⇒ χ) ⇒ χ) ∧ ((β ⇒ χ) ⇒ χ)) ⊢ (((α ∧ β) ⇒ χ) ⇒ χ)
    ¬¬-conj = {!!}

    bind : {Γ : Cxt} {α β χ : Form Γ 1st} → α ⊢ ((β ⇒ χ) ⇒ χ) → ((α ⇒ χ) ⇒ χ) ⊢ ((β ⇒ χ) ⇒ χ)
    bind p = {!!}

    ¬-ex-falso : {Γ : Cxt} {φ χ : Form Γ 1st} → χ ⊢ (φ ⇒ χ)
    ¬-ex-falso = impl₁ conj-elimₗ

  module TranslationBase where
    ¬_ : {Γ : Cxt} → Form Γ 1st → Form Γ 1st
    ¬ φ = φ ⇒ ⊥

    _* : {Γ : Cxt} → Form Γ 1st → Form Γ 1st
    (s ≈ t) * = ¬ ¬ (s ≈ t)
    at r xs * = ¬ ¬ (at r xs)
    ⊤       * = ⊤
    ⊥       * = ¬ ¬ ⊥
    (φ ∧ ψ) * = (φ *) ∧ (ψ *)
    (φ ∨ ψ) * = ¬ ¬ ((φ *) ∨ (ψ *))
    (φ ⇒ ψ) * = (φ *) ⇒ (ψ *)
    FA φ    * = FA (φ *)
    EX φ    * = ¬ ¬ EX (φ *)

    subs-* : {Γ Δ : Cxt} (π : {σ : Ty} → σ ∈ Γ → Term Δ σ) (α : Form Γ 1st) → subs π (α *) ≡ (subs π α) *
    subs-* π (s ≈ t)   = refl
    subs-* π (at r xs) = refl
    subs-* π ⊤         = refl
    subs-* π ⊥         = refl
    subs-* π (α ∧ β)   = cong₂ _∧_ (subs-* π α) (subs-* π β)
    subs-* π (α ∨ β)   = cong ¬_ (cong ¬_ (cong₂ _∨_ (subs-* π α) (subs-* π β)))
    subs-* π (α ⇒ β)   = cong₂ _⇒_ (subs-* π α) (subs-* π β)
    subs-* π (FA α)    = cong FA (subs-* _ α)
    subs-* π (EX α)    = cong ¬_ (cong ¬_ (cong EX (subs-* _ α)))

    weaken-¬ : {Γ : Cxt} {τ : Ty} → (α : Form Γ 1st) → ¬ (weaken {τ} α) ≡ weaken (¬ α)
    weaken-¬ _ = refl

    weaken-¬¬ : {Γ : Cxt} {τ : Ty} → (α : Form Γ 1st) → ¬ ¬ (weaken {τ} α) ≡ weaken (¬ ¬ α)
    weaken-¬¬ _ = refl --trans (cong ¬_ (weaken-¬ α)) (weaken-¬ (¬ α))

  module TranslationProofs (ax : Axioms) where
    open TranslationBase
    open Proof min ax

    stable : {Γ : Cxt} → (φ : Form Γ 1st) → (¬ ¬ (φ *)) ⊢ (φ *)
    stable (s ≈ t)   = {!!}
    stable (at r xs) = {!!}
    stable ⊤         = {!!}
    stable ⊥         = {!!}
    stable (φ ∧ ψ)   = {!!}
    stable (φ ∨ ψ)   = {!!}
    stable (φ ⇒ ψ)   = {!!}
    stable (FA φ)    = {!!}
    stable (EX φ)    = {!!}

    ex-falso : {Γ : Cxt} → (φ : Form Γ 1st) → ⊥ ⊢ (φ *)
    ex-falso (s ≈ t)   = {!!}
    ex-falso (at r xs) = {!!}
    ex-falso ⊤         = {!!}
    ex-falso ⊥         = {!!}
    ex-falso (φ ∧ ψ)   = {!!}
    ex-falso (φ ∨ ψ)   = {!!}
    ex-falso (φ ⇒ ψ)   = {!!}
    ex-falso (FA φ)    = {!!}
    ex-falso (EX φ)    = {!!}

    collect₁ : {Γ : Cxt} → (φ : Form Γ coh) → ((relax φ) *) ⊢ (¬ ¬ (relax φ))
    collect₁ (s ≈ t)   = {!!}
    collect₁ (at r xs) = {!!}
    collect₁ ⊤         = {!!}
    collect₁ ⊥         = {!!}
    collect₁ (φ ∧ ψ)   = {!!}
    collect₁ (φ ∨ ψ)   = {!!}
    collect₁ (EX φ)    = {!!}

    collect₂ : {Γ : Cxt} → (φ : Form Γ coh) → (¬ ¬ (relax φ)) ⊢ ((relax φ) *)
    collect₂ (s ≈ t)   = {!!}
    collect₂ (at r xs) = {!!}
    collect₂ ⊤         = {!!}
    collect₂ ⊥         = {!!}
    collect₂ (φ ∧ ψ)   = {!!}
    collect₂ (φ ∨ ψ)   = {!!}
    collect₂ (EX φ)    = {!!}

  module _ (ax ax' : Axioms) (mode : Mode) where
    open Proof mode ax  using (_⊢_)
    open Proof mode ax' renaming (_⊢_ to _⊢'_)

    module _ (lift : {Γ : Cxt} {α β : Form Γ 1st} → ax α β → α ⊢' β) where
      interpret : {Γ : Cxt} {α β : Form Γ 1st} → α ⊢ β → α ⊢' β
      interpret (axiom a) = lift a
      interpret identity = identity
      interpret (substitution π p) = substitution π (interpret p)
      interpret (cut p q) = cut (interpret p) (interpret q)
      interpret eq-refl = eq-refl
      interpret eq-subst = eq-subst
      interpret top-intr = top-intr
      interpret conj-elimₗ = conj-elimₗ
      interpret conj-elimᵣ = conj-elimᵣ
      interpret (conj-intr p q) = conj-intr (interpret p) (interpret q)
      interpret (bot-elim {k}) = bot-elim {k}
      interpret disj-intrₗ = disj-intrₗ
      interpret disj-intrᵣ = disj-intrᵣ
      interpret (disj-elim p q) = disj-elim (interpret p) (interpret q)
      interpret (impl₁ p) = impl₁ (interpret p)
      interpret (impl₂ p) = impl₂ (interpret p)
      interpret (forall₁ p) = forall₁ (interpret p)
      interpret (forall₂ p) = forall₂ (interpret p)
      interpret (exists₁ p) = exists₁ (interpret p)
      interpret (exists₂ p) = exists₂ (interpret p)
      interpret (lem {k}) = lem {k}

  module _ (ax : Axioms) where
    open TranslationBase

    data ax* : {Γ : Cxt} → Form Γ 1st → Form Γ 1st → Set where
      lift : {Γ : Cxt} {α β : Form Γ 1st} → ax α β → ax* (α *) (β *)

    open TranslationProofs ax*

    open Proof class ax  using (_⊢_)
    open Proof min   ax* renaming (_⊢_ to _⊢ᵐ_)

    sound : {Γ : Cxt} {α β : Form Γ 1st} → α ⊢ β → (α *) ⊢ᵐ (β *)
    sound (axiom a)          = {!!}
    sound identity           = {!!}
    sound (substitution π p) = {!!}
    sound (cut p q)          = {!!}
    sound eq-refl            = {!!}
    sound eq-subst           = {!!}
    sound top-intr           = {!!}
    sound conj-elimₗ         = {!!}
    sound conj-elimᵣ         = {!!}
    sound (conj-intr p q)    = {!!}
    sound bot-elim           = {!!}
    sound disj-intrₗ         = {!!}
    sound disj-intrᵣ         = {!!}
    sound (disj-elim p q)    = {!!}
    sound (impl₁ p)          = {!!}
    sound (impl₂ p)          = {!!}
    sound (forall₁ p)        = {!!}
    sound (forall₂ p)        = {!!}
    sound (exists₁ p)        = {!!}
    sound (exists₂ p)        = {!!}
    sound lem                = {!!}

  module _ (ax : {Γ : Cxt} → Form Γ coh → Form Γ coh → Set) where
    data ax' : {Γ : Cxt} → Form Γ 1st → Form Γ 1st → Set where
      lift : {Γ : Cxt} {α β : Form Γ coh} → ax α β → ax' (relax α) (relax β)

    open TranslationBase

    module C = Proof class ax'
    module M = Proof min   (ax* ax')
    module T = Proof min   ax'

    trick : {Γ : Cxt} {α : Form Γ coh} → relax α C.⊢ relax ⊥ → relax α T.⊢ relax ⊥
    trick p = interpret (ax* ax') ax' min
      (λ { (lift (lift a)) → go-axiom a })
      (go-result (sound ax' p))
      where
      go-axiom : {Γ : Cxt} {α β : Form Γ coh} → ax α β → (relax α *) T.⊢ (relax β *)
      go-axiom a = T.cut (collect₁ _) (T.cut (T.¬¬-monotone (T.axiom (lift a))) (collect₂ _))
        where open TranslationProofs ax'

      go-result : {Γ : Cxt} {α : Form Γ coh} → (relax α *) M.⊢ (relax ⊥ *) → relax α M.⊢ relax ⊥
      go-result p = M.cut M.return (M.cut (collect₂ _) (M.cut p (M.cut (collect₁ _) M.escape)))
        where open TranslationProofs (ax* ax')
