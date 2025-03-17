{-# OPTIONS --type-in-type #-}

open import Data.Nat hiding (_≤_)
open import Function using (_∘_)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import 10-Lecture
open import 11-Lecture

---------------------------------------------------------------------------
-- Monads, categorically
---------------------------------------------------------------------------

record Monad (C : Category) : Set where
  open Category C
  open Functor
  open NaturalTransformation

  field
    functor : Functor C C

  private
    M = functor

  field
    returnNT : NaturalTransformation idFunctor M
    joinNT   : NaturalTransformation (compFunctor M M) M

  return = transform returnNT
  join   = transform joinNT

  field
    returnJoin : {X : Obj}    -> comp (return (act M X)) (join X) ≡ id
    mapReturnJoin : {X : Obj} -> comp (fmap M (return X)) (join X) ≡ id
    joinJoin : {X : Obj} -> comp (join (act M X)) (join X) ≡ comp (fmap M (join X)) (join X)

  bind : {X Y : Obj} → Hom X (act M Y) → Hom (act M X) (act M Y)
  bind {X} {Y} f = comp (fmap M f) (join Y)

  open Functor M public

---------------------------------------------------------------------------
-- Hutton's Razor is a monad
---------------------------------------------------------------------------

module _ where

  open Monad
  open NaturalTransformation

  data Expr (X : Set) : Set where
    var : X -> Expr X
    num : ℕ -> Expr X
    _+E_ : Expr X -> Expr X -> Expr X

  mapExpr : {X Y : Set} -> (X -> Y) -> Expr X -> Expr Y
  mapExpr f (var x) = var (f x)
  mapExpr f (num x) = num x
  mapExpr f (e +E e') = mapExpr f e +E mapExpr f e'

  EXPR : Functor SET SET
  Functor.act EXPR = Expr
  Functor.fmap EXPR = mapExpr
  Functor.identity EXPR = ext lemma
    where
    lemma : {X : Set} → (x : Expr X) → mapExpr (Category.id SET) x ≡ x
    lemma (var x) = refl
    lemma (num n) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  Functor.homomorphism EXPR {X} {f = f} {g} = ext lemma
    where
    lemma : (x : Expr X) → mapExpr (Category.comp SET f g) x ≡ mapExpr g (mapExpr f x)
    lemma (var x) = refl
    lemma (num n) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')

  joinExpr : {X : Set} -> Expr (Expr X) -> Expr X
  joinExpr (var ee) = ee
  joinExpr (num n) = num n
  joinExpr (ee +E ee') = joinExpr ee +E joinExpr ee'

  EXPR-MONAD : Monad SET
  functor EXPR-MONAD = EXPR
  transform (returnNT EXPR-MONAD) X = var
  natural (returnNT EXPR-MONAD) X Y f = refl
  transform (joinNT EXPR-MONAD) X = joinExpr
  natural (joinNT EXPR-MONAD) X Y f = ext lemma
    where
    lemma :(x : Expr (Expr X)) →
      Category.comp SET (mapExpr (mapExpr f)) joinExpr x ≡
      Category.comp SET joinExpr (mapExpr f) x
    lemma (var x) = refl
    lemma (num n) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  returnJoin EXPR-MONAD = refl
  mapReturnJoin EXPR-MONAD {X} = ext lemma
    where
    lemma : (x : Expr X) → joinExpr (mapExpr var x) ≡ x
    lemma (var x) = refl
    lemma (num n) = refl
    lemma (e +E e') = cong₂ _+E_ (lemma e) (lemma e')
  joinJoin EXPR-MONAD {X} = ext lemma
    where
    lemma : (x : Expr (Expr (Expr X))) →
      joinExpr (joinExpr x) ≡ joinExpr (mapExpr joinExpr x)
    lemma (var x) = refl
    lemma (num x) = refl
    lemma (eee +E eee₁) = cong₂ _+E_ (lemma eee) (lemma eee₁)








---------------------------------------------------------------------------
-- Adding a bottom is a monad
---------------------------------------------------------------------------

module _ where

  open Preorder
  open MonotoneMap
  open Functor
  open Monad
  open NaturalTransformation

  data Lift (P : Set) : Set where
    η : P → Lift P
    ⊥ : Lift P

  data Lift≤ (P : Preorder) : Lift (Carrier P) -> Lift (Carrier P) -> Set where
    bot : (q : Lift (Carrier P)) → Lift≤ P ⊥ q
    η≤ : {p p' : Carrier P} → _≤_ P p p' → Lift≤ P (η p) (η p')

  LIFT : Functor PREORDER PREORDER
  Carrier (act LIFT P) = Lift (Carrier P)
  _≤_ (act LIFT P) = Lift≤ P
  reflexive (act LIFT P) {η x} = η≤ (reflexive P)
  reflexive (act LIFT P) {⊥} = bot ⊥
  transitive (act LIFT P) (bot _) _ = bot _
  transitive (act LIFT P) (η≤ x) (η≤ x₁) = η≤ (transitive P x x₁)
  propositional (act LIFT P) (bot _) (bot _) = refl
  propositional (act LIFT P) (η≤ x) (η≤ x₁) = cong η≤ (propositional P x x₁)
  fun (fmap LIFT f) (η x) = η (fun f x)
  fun (fmap LIFT f) ⊥ = ⊥
  monotone (fmap LIFT f) (η x) (η x₁) (η≤ x₂) = η≤ (monotone f x x₁ x₂)
  monotone (fmap LIFT f) (η x) ⊥ ()
  monotone (fmap LIFT f) ⊥ (η x) (bot .(η x)) = bot (fun (fmap LIFT f) (η x))
  monotone (fmap LIFT f) ⊥ ⊥ (bot .⊥) = bot (fun (fmap LIFT f) ⊥)
  identity LIFT {X} = eqMonotoneMap (ext λ { (η x) → refl ; ⊥ → refl })
  homomorphism LIFT {X} {f = f} {g} = eqMonotoneMap (ext λ { (η x) → refl ; ⊥ → refl})

  LIFT-MONAD : Monad PREORDER
  functor LIFT-MONAD = LIFT
  fun (transform (returnNT LIFT-MONAD) X) = η
  monotone (transform (returnNT LIFT-MONAD) X) x y = η≤
  natural (returnNT LIFT-MONAD) X Y f = refl
  fun (transform (joinNT LIFT-MONAD) X) (η x) = x
  fun (transform (joinNT LIFT-MONAD) X) ⊥ = ⊥
  monotone (transform (joinNT LIFT-MONAD) X) (η x) (η x₁) (η≤ x₂) = x₂
  monotone (transform (joinNT LIFT-MONAD) X) (η x) ⊥ ()
  monotone (transform (joinNT LIFT-MONAD) X) ⊥ (η x) (bot .(η x)) = bot (fun (transform (joinNT LIFT-MONAD) X) (η x))
  monotone (transform (joinNT LIFT-MONAD) X) ⊥ ⊥ (bot .⊥) = bot (fun (transform (joinNT LIFT-MONAD) X) ⊥)
  natural (joinNT LIFT-MONAD) X Y f = eqMonotoneMap (ext λ { (η x) → refl ; ⊥ → refl })
  returnJoin LIFT-MONAD = eqMonotoneMap refl
  mapReturnJoin LIFT-MONAD {X} = eqMonotoneMap (ext λ { (η x) → refl ; ⊥ → refl })
  joinJoin LIFT-MONAD {X} = eqMonotoneMap (ext λ { (η x) → refl ; ⊥ → refl })
