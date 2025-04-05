{-# OPTIONS --cubical --safe --postfix-projections #-}

module GroupEquiv where

-- Isomorphisms of groups induce paths in Group

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Group.Base
  using (isGroup; Group; isMorph; morph)
  renaming (Iso to GIso)

variable
  ℓ ℓ' : Level
  A B : Type ℓ
  
module _ (G : Type ℓ) (e : G) (op : G → G) (_◎_ : G → G → G) where
  record isGroupStruc : Type ℓ where
    constructor is-group-struc
    field
      lUnit : ∀ g → e ◎ g ≡ g
      rUnit : ∀ g → g ◎ e ≡ g
      lCancel : ∀ g → op g ◎ g ≡ e
      rCancel : ∀ g → g ◎ op g ≡ e
      assoc : ∀ f g h → (f ◎ g) ◎ h ≡ f ◎ (g ◎ h)

module _ {G : Type ℓ} {e : G} {op : G → G} {_◎_ : G → G → G} (Gset : isSet G) where
  open isGroupStruc
  isPropIsGroupStruc : isProp (isGroupStruc G e op _◎_)
  isPropIsGroupStruc s t i .lUnit g = Gset _ _ (s .lUnit g) (t .lUnit g) i
  isPropIsGroupStruc s t i .rUnit g = Gset _ _ (s .rUnit g) (t .rUnit g) i
  isPropIsGroupStruc s t i .lCancel g = Gset _ _ (s .lCancel g) (t .lCancel g) i
  isPropIsGroupStruc s t i .rCancel g = Gset _ _ (s .rCancel g) (t .rCancel g) i
  isPropIsGroupStruc s t i .assoc f g h
    = Gset _ _ (s .assoc f g h) (t .assoc f g h) i

module _ where
  open Group

  groupLaws
    : (𝔾 : Group ℓ)
    → isGroupStruc
        (𝔾 .type)
        (𝔾 .groupStruc .isGroup.id)
        (𝔾 .groupStruc .isGroup.inv)
        (𝔾 .groupStruc .isGroup.comp)
  groupLaws 𝔾 = is-group-struc lUnit rUnit lCancel rCancel assoc
    where
    open isGroup (𝔾 .groupStruc)

module Isomorph
    (𝔾 : Group ℓ) (ℍ : Group ℓ)
    (𝔾≅ℍ : GIso 𝔾 ℍ)
  where
  open Group 𝔾 renaming (type to G; groupStruc to Ggrp; setStruc to Gset)
  open Group ℍ renaming (type to H; groupStruc to Hgrp; setStruc to Hset)
  open isGroup Ggrp renaming
    ( id to eᴳ ; inv to opᴳ ; comp to _⊙_
    ; lUnit to lUnitᴳ
    ; rUnit to rUnitᴳ
    ; lCancel to lCancelᴳ
    ; rCancel to rCancelᴳ
    ; assoc to assocᴳ
    )
  open isGroup Hgrp renaming
    ( id to eᴴ ; inv to opᴴ ; comp to _◎_
    ; lUnit to lUnitᴴ
    ; rUnit to rUnitᴴ
    ; lCancel to lCancelᴴ
    ; rCancel to rCancelᴴ
    ; assoc to assocᴴ
    )

  open GIso 𝔾≅ℍ
    renaming (fun to Θ; inv to Φ; rightInv to sect; leftInv to retr)

  θ = fst Θ
  θ-comp = snd Θ

  φ = fst Φ

  θ-unit : θ eᴳ ≡ eᴴ
  θ-unit
    = θ eᴳ ≡⟨ sym (rUnitᴴ _) ⟩
      θ eᴳ ◎ eᴴ ≡[ i ]⟨ θ eᴳ ◎ rCancelᴴ (θ eᴳ) (~ i) ⟩
      θ eᴳ ◎ (θ eᴳ ◎ opᴴ (θ eᴳ)) ≡⟨ sym (assocᴴ _ _ _) ⟩
      (θ eᴳ ◎ θ eᴳ) ◎ opᴴ (θ eᴳ) ≡[ i ]⟨ θ-comp eᴳ eᴳ (~ i) ◎ opᴴ (θ eᴳ) ⟩
      θ (eᴳ ⊙ eᴳ) ◎ opᴴ (θ eᴳ) ≡[ i ]⟨ θ (lUnitᴳ eᴳ i) ◎ opᴴ (θ eᴳ) ⟩
      θ eᴳ ◎ opᴴ (θ eᴳ) ≡⟨ rCancelᴴ _ ⟩
      eᴴ ∎

  θ-op : ∀ g → θ (opᴳ g) ≡ opᴴ (θ g)
  θ-op g = θ (opᴳ g) ≡⟨ sym (lUnitᴴ _) ⟩
           eᴴ ◎ θ (opᴳ g) ≡[ i ]⟨ lCancelᴴ (θ g) (~ i) ◎ θ (opᴳ g) ⟩
           (opᴴ (θ g) ◎ θ g) ◎ θ (opᴳ g) ≡⟨ assocᴴ _ _ _ ⟩
           opᴴ (θ g) ◎ (θ g ◎ θ (opᴳ g)) ≡[ i ]⟨ opᴴ (θ g) ◎ θ-comp g (opᴳ g) (~ i) ⟩
           opᴴ (θ g) ◎ θ (g ⊙ opᴳ g) ≡[ i ]⟨ opᴴ (θ g) ◎ θ (rCancelᴳ g i) ⟩
           opᴴ (θ g) ◎ θ eᴳ ≡[ i ]⟨ opᴴ (θ g) ◎ θ-unit i ⟩
           opᴴ (θ g) ◎ eᴴ ≡⟨ rUnitᴴ _ ⟩
           opᴴ (θ g) ∎


  IGH : Iso G H
  IGH = iso θ φ sect retr

  G≡H : G ≡ H
  G≡H = isoToPath IGH

  GHset : PathP (λ i → isSet (G≡H i)) Gset Hset
  GHset = isProp→PathP (λ _ → isPropIsSet) G≡H Gset Hset

  e-path : PathP (λ i → G≡H i) eᴳ eᴴ
  e-path i = glue (λ{ (i = i0) → eᴳ ; (i = i1) → eᴴ }) (θ-unit i)

  op-path : PathP (λ i → G≡H i → G≡H i) opᴳ opᴴ
  op-path i g
    = glue (λ where
                (i = i0) → opᴳ g
                (i = i1) → opᴴ g)
        (hcomp (λ k → λ where
                  (i = i0) → θ-op g (~ k)
                  (i = i1) → opᴴ g) (opᴴ (unglue (i ∨ ~ i) g)))

  cmp-path : PathP (λ i → G≡H i → G≡H i → G≡H i) _⊙_ _◎_
  cmp-path i g h
    = glue (λ where
                (i = i0) → g ⊙ h
                (i = i1) → g ◎ h)
        (hcomp (λ k → λ where
                  (i = i0) → θ-comp g h (~ k)
                  (i = i1) → g ◎ h) (unglue (i ∨ ~ i) g ◎ unglue (i ∨ ~ i) h))

  structure-path
    : PathP (λ i → isGroupStruc (G≡H i) (e-path i) (op-path i) (cmp-path i))
        (groupLaws 𝔾) (groupLaws ℍ)
  structure-path i
    = hcomp (λ where
          k (i = i0) → groupLaws 𝔾
          k (i = i1) → isPropIsGroupStruc Hset pushed (groupLaws ℍ) k) pushed
    where
    Law : I → Type _
    Law k = isGroupStruc (G≡H k) (e-path k) (op-path k) (cmp-path k)
    pushed : Law i
    pushed = transp (λ k → Law (i ∧ k)) (~ i) (groupLaws 𝔾)

  𝔾≡ℍ : 𝔾 ≡ ℍ
  𝔾≡ℍ i .Group.type = G≡H i
  𝔾≡ℍ i .Group.setStruc = GHset i
  𝔾≡ℍ i .Group.groupStruc .isGroup.id = e-path i
  𝔾≡ℍ i .Group.groupStruc .isGroup.inv = op-path i
  𝔾≡ℍ i .Group.groupStruc .isGroup.comp = cmp-path i
  𝔾≡ℍ i .Group.groupStruc .isGroup.lUnit = structure-path i .isGroupStruc.lUnit
  𝔾≡ℍ i .Group.groupStruc .isGroup.rUnit = structure-path i .isGroupStruc.rUnit
  𝔾≡ℍ i .Group.groupStruc .isGroup.lCancel = structure-path i .isGroupStruc.lCancel
  𝔾≡ℍ i .Group.groupStruc .isGroup.rCancel = structure-path i .isGroupStruc.rCancel
  𝔾≡ℍ i .Group.groupStruc .isGroup.assoc = structure-path i .isGroupStruc.assoc
