open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Category.Category

---------------------------------------------------------------------------
-- Kleisli categories
---------------------------------------------------------------------------

open import Category.Solver

module Category.Kleisli {C : Category} where

  open Category
  open Monad
  open NaturalTransformation

  Kleisli : Monad C -> Category
  Obj (Kleisli M) = Obj C
  Hom (Kleisli M) X Y = Hom C X (act M Y)
  id (Kleisli M) = return M _
  comp (Kleisli M) f g = comp C f (bind M g)
  identityʳ (Kleisli M) {f = f} = begin
    comp C f (comp C (fmap M (return M _)) (join M _))
      ≡⟨ cong (comp C f) (mapReturnJoin M) ⟩
    comp C f (id C)
      ≡⟨ identityʳ C ⟩
    f ∎ where open ≡-Reasoning
  identityˡ (Kleisli M) {f = g} = C ⊧begin
    compSyn < return M _ > (compSyn (fmapSyn (functor M) < g >) < join M _ >)
      ≡⟦ solveCat refl ⟧
    -[ < return M _ > ；Syn fmapSyn (functor M) < g > ]- ；Syn < join M _ >
      ≡⟦ reduced (rd , rq (sym (natural (returnNT M) _ _ g))) ⟧
    -[  < g > ；Syn < return M _ > ]- ；Syn < join M _ >
      ≡⟦ solveCat refl ⟧
    < g > ；Syn -[ < return M _ > ；Syn < join M _ > ]-
      ≡⟦ reduced ((rq (returnJoin M) , rd)) ⟧
    < g > ；Syn -[ idSyn ]-
      ≡⟦ solveCat refl ⟧
    < g >
      ⟦∎⟧
  assoc (Kleisli M) {f = f} {g} {h} = C ⊧begin
   compSyn < f > (compSyn (fmapSyn (functor M) (compSyn < g > (compSyn (fmapSyn (functor M) < h >) < join M _ >))) < join M _ > )
      ≡⟦ solveCat refl ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn -[ fmapSyn (functor M) < join M _ > ；Syn < join M _ > ]-
      ≡⟦ reduced (rq (sym (joinJoin M)) , rd , rd , rd) ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn -[ < join M _ > ；Syn < join M _ > ]-
     ≡⟦ solveCat refl ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn -[ fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn < join M _ > ]- ；Syn < join M _ >
     ≡⟦ reduced (rd , rq (natural (joinNT M) _ _ h) , rd , rd) ⟧
   < f > ；Syn (fmapSyn (functor M) < g >) ；Syn -[ < join M _ > ；Syn fmapSyn (functor M) < h > ]- ；Syn < join M _ >
     ≡⟦ solveCat refl ⟧
   compSyn (compSyn < f > (compSyn (fmapSyn (functor M) < g >) < join M _ >))
    (compSyn (fmapSyn (functor M) < h >) < join M _ >)
      ⟦∎⟧
