
open import Data.Maybe

open import Relation.Binary.PropositionalEquality

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Axiom.Extensionality.Propositional

open import 10-Lecture using (ext
                             ; Monoid; MonoidMorphism
                             ; Preorder; MonotoneMap; eqMonotoneMap
                             ; Category
                             ; SET; MONOID; PREORDER)

open Category

---------------------------------------------------------------------------
-- Functors in Haskell
---------------------------------------------------------------------------

-- See 11-Lecture.hs


















---------------------------------------------------------------------------
-- Functors in Haskell
---------------------------------------------------------------------------

-- A functor is a "morphism of categories": we translate objects to
-- objects, and morphisms to morphisms, in such a way that the
-- structure is preserved.

record Functor (C D : Category) : Set where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {X Y} (f : C.Hom X Y) → D.Hom (act X) (act Y)

  field -- laws
    identity     : ∀ {X} → fmap (C.id {X}) ≡ D.id {act X}
    homomorphism : ∀ {X Y Z} {f : C.Hom X Y}{g : C.Hom Y Z} →
                   fmap (C.comp f g) ≡ D.comp (fmap f) (fmap g)
open Functor

---------------------------------------------------------------------------
-- Tree is a functor
---------------------------------------------------------------------------

-- Here is the Tree type from Haskell again, together with its fmap instance:

data Tree (X : Set) : Set where
  leaf : Tree X
  node : Tree X -> X -> Tree X -> Tree X

tree-map : {X Y : Set} → (X → Y) → Tree X → Tree Y
tree-map f leaf = leaf
tree-map f (node l x  r) = node (tree-map f l) (f x) (tree-map f r)

-- But, even better, we can now *prove* that it satisfies the laws!

TREE : Functor SET SET
act TREE = Tree
fmap TREE = tree-map
identity TREE {X} = ext lemma
  where
  lemma : (t : Tree X) → tree-map (λ x → x) t ≡ t
  lemma leaf = refl
  lemma (node l x r) = cong₂ (λ l r → node l x r) (lemma l) (lemma r)
homomorphism TREE {X} {f = f} {g} = ext lemma
  where
  lemma : (t : Tree X) → tree-map (λ x → g (f x)) t ≡ tree-map g (tree-map f t)
  lemma leaf = refl
  lemma (node l x r) = cong₂ (λ l r → node l (g (f x)) r) (lemma l) (lemma r)










--------------------------------------------------------------------------
-- Forgetful mappings are functors
---------------------------------------------------------------------------

-- Importantly, functors can also be between different categories --
-- that's how we use them to transfer constructions and results from
-- one category to another.

module _ where -- we temporarily open the Monoid records

  open Monoid
  open MonoidMorphism

  forgetMonoid : Functor MONOID SET
  act forgetMonoid M = Carrier M
  fmap forgetMonoid f = fun f
  identity forgetMonoid = refl
  homomorphism forgetMonoid = refl

--------------------------------------------------------------------------
-- "Canonical" constructions are often functors
---------------------------------------------------------------------------

module _ where

  open Preorder
  open MonotoneMap

  smallestOrder : Functor SET PREORDER
  Carrier (act smallestOrder X) = X
  _≤_ (act smallestOrder X) x y = x ≡ y
  reflexive (act smallestOrder X) = refl
  transitive (act smallestOrder X) = trans
  propositional (act smallestOrder X) = uip
  fun (fmap smallestOrder f) = f
  monotone (fmap smallestOrder f) x y = cong f
  identity smallestOrder  = eqMonotoneMap refl
  homomorphism smallestOrder = eqMonotoneMap refl










  -- Exercise: is there a greatest order? ("chaotic")


-------------------------------
-- How to prove Functors equal
-------------------------------

eqFunctor : {C D : Category}{F G : Functor C D} ->
            (p : act F ≡ act G) ->
            (∀ {A B} → subst (λ z → Hom C A B -> Hom D (z A) (z B)) p (fmap F) ≡ (fmap G {A} {B})) ->
            F ≡ G
eqFunctor {G = G} refl q with iext (λ {A} → iext (λ {B} → q {A} {B}))
  where   iext = implicit-extensionality ext
... | refl = eqFunctor' {G = G} (implicit-extensionality ext λ {A} → uip _ _) (iext (iext (iext (iext (iext (uip _ _)))))) where
  iext = implicit-extensionality ext
  eqFunctor' : ∀ {C} {D} {G : Functor C D}
               {identity' identity'' : {A : Obj C} → fmap G {A} (Category.id C) ≡ Category.id D}
               {homomorphism' homomorphism'' : {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} →
               (_≡_ {A = ∀ {A} → fmap G {A} (Category.id C) ≡ Category.id D} identity' identity'') ->
               (_≡_ {A = {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} homomorphism' homomorphism'') ->
             _≡_ {A = Functor C D} (record { act = act G; fmap = fmap G; identity = identity'; homomorphism = homomorphism' })
                                   (record { act = act G; fmap = fmap G; identity = identity''; homomorphism = homomorphism'' })
  eqFunctor' refl refl = refl


--------------------------------------------------------------------------
-- The category of categories
---------------------------------------------------------------------------

compFunctor : {𝓒 𝓓 𝓔 : Category} -> Functor 𝓒 𝓓 → Functor 𝓓 𝓔 → Functor 𝓒 𝓔
act (compFunctor ℱ 𝒢) X = act 𝒢 (act ℱ X)
fmap (compFunctor ℱ 𝒢) f = fmap 𝒢 (fmap ℱ f)
identity (compFunctor ℱ 𝒢) {X} rewrite identity ℱ {X} = identity 𝒢
homomorphism (compFunctor ℱ 𝒢) {X} {Y} {Z} {f} {g}
  rewrite homomorphism ℱ {X} {Y} {Z} {f} {g} = homomorphism 𝒢

idFunctor : {𝓒 : Category} -> Functor 𝓒 𝓒
act idFunctor X = X
fmap idFunctor f = f
identity idFunctor = refl
homomorphism idFunctor = refl

CAT : Category
Obj CAT = Category
Hom CAT = Functor
id CAT = idFunctor
comp CAT = compFunctor
assoc CAT = eqFunctor refl refl
identityˡ CAT = eqFunctor refl refl
identityʳ CAT = eqFunctor refl refl














--------------------------------------------------------------------------
-- Natural transformations
--------------------------------------------------------------------------

-- What is a morphism between functors?

record NaturalTransformation {C D : Category}
                             (F G : Functor C D) : Set where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    transform   : ∀ X → D.Hom (F.act X) (G.act X)
    natural     : ∀ X Y (f : C.Hom X Y) →
                  D.comp (F.fmap f) (transform Y) ≡ D.comp (transform X) (G.fmap f)
open NaturalTransformation

-- So a natural transformation is a family of morphisms F X → G X,
-- which is compatible with the fmap of F and G: we get the same
-- result if we first fmap and then translate, or if we first
-- translate and then fmap.

--------------------------------------------------------------------------
-- root is a natural transformation
---------------------------------------------------------------------------

map-Maybe : ∀ {X Y : Set} → (X → Y) → Maybe X → Maybe Y
map-Maybe f (just x) = just (f x)
map-Maybe f nothing = nothing

MAYBE : Functor SET SET
act MAYBE = Maybe
fmap MAYBE = map-Maybe
identity MAYBE = ext lemma
  where
  lemma : ∀{X : Set} → (x : Maybe X) → map-Maybe (λ x₁ → x₁) x ≡ x
  lemma (just x) = refl
  lemma nothing = refl
homomorphism MAYBE = ext lemma
  where
  lemma : ∀{X Y Z : Set} {f : Hom SET X Y} {g : Hom SET Y Z} → (x : Maybe X) → fmap MAYBE (comp SET f g) x ≡ comp SET (fmap MAYBE f) (fmap MAYBE g) x
  lemma (just x) = refl
  lemma nothing = refl

-- Exercise: is there a more appropriate target category for MAYBE?

root : NaturalTransformation TREE MAYBE
transform root X leaf = nothing
transform root X (node l x r) = just x
natural root X Y f = ext λ { leaf → refl ; (node l x r) → refl }
