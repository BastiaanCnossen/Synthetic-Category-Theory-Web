# Changing the base of global relative functors

Postcompose the universal relative family's base triangle and factor that
family into the target relative functor category. Its complete family beta
computes the resulting categorical functor. Native reflection supplies
its triangle over the ordinary functor category with its actual image.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.RelativeBaseChange where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-square-cell)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying
open import SCT.VolumeI.Chapter01.Section09.RelativeFunctorCategories
open import SCT.VolumeI.Chapter01.Section09.RelativeFamilyComparisons

module BaseChange {Γ : Context} {S T : CAT Γ} (u : MAP S T) (A B : CategoryOverBase S) where
  module Source = RelativeFunctorCategory A B
  module Native = RelativeFamilies A B
  module Target = RelativeFunctorCategory (postcompose-base u A) (postcompose-base u B)
  module Changed = RelativeFamilies (postcompose-base u A) (postcompose-base u B)
  private
    C = CategoryOverBase.category A
    D = CategoryOverBase.category B
    p = CategoryOverBase.map A
    q = CategoryOverBase.map B
    eD = funEval {C = C} {D = D}

  universal-family : Source.Family Source.category
  universal-family = functor-over
    (Cone.left (Native.evaluated-cone Source.fiber)) (Cone.match (Native.evaluated-cone Source.fiber))

  changed-family : Target.Family Source.category
  changed-family = functor-over (FunctorOverBase.functor universal-family)
    (post-square-cell u pr₂ p q (FunctorOverBase.functor universal-family) (FunctorOverBase.cell universal-family))

  private
    module Chosen = Target.ChosenFamily changed-family

  functor : MAP Source.category Target.category
  functor = Chosen.factor

  computation : ConeIdentification₁
    (Changed.family-cone (Target.evaluated-family functor)) (Changed.family-cone changed-family)
  computation = Changed.FamilyComputation.comparison changed-family

  inclusion-comparison : (Target.inclusion ∘ functor) =₁ Source.inclusion
  inclusion-comparison = reflect eD (funUniversal C D) (Target.inclusion ∘ functor) Source.inclusion
    Chosen.underlying-computation

  inclusion-image : evaluate-cong eD inclusion-comparison =₂ Chosen.underlying-computation
  inclusion-image = reflect-β-One eD (funUniversal C D) (Target.inclusion ∘ functor) Source.inclusion
    Chosen.underlying-computation

  over-functors : FunctorOverBase
    (category-over Source.category Source.inclusion) (category-over Target.category Target.inclusion)
  over-functors = functor-over functor inclusion-comparison
```
