# Cartesian forgetful squares

A triangle over the base gives a map between the defining fibers of
relative functor categories. The square of forgetful functors is a
pullback. We retain the square obtained from the whole cospan map,
including its specified identification.

This module uses the fiber description of postcomposition. Comparison
with evaluation-based `Postcompose.functor` is a separate computation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ForgetSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanCartesian 𝒯 P using (rightSquareOf; module CartesianProjection)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P

module Postcomposition {K C D S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} (u : FunctorOver f g) where
  underlying = FunctorLift.lift u
  left = funPost {C = K} underlying
  source = funPost {C = K} f
  target = funPost {C = K} g
  named = nameFun k

  cospan : CospanMap source named target named
  cospan = record
    { left = left ; right = id One ; base = id (Fun K S)
    ; leftSquare = (comp-unitˡ source) ⁻¹ ∙
        (funPost-cong (FunctorLift.comparison u) ∙ funPost-comp underlying g)
    ; rightSquare = (comp-unitˡ named) ⁻¹ ∙ comp-unitʳ named }

  abstract
    right-isPullback : IsPullback (rightSquareOf cospan)
    right-isPullback = degenerate-pullback (id-isEquiv (Fun K S))
      (rightSquareOf cospan) (id-isEquiv One)

  module Cartesian = CartesianProjection cospan right-isPullback
    using (projectionSquare; projection-square-isPullback)

  functor : MAP (FunOver k f) (FunOver k g)
  functor = CospanMap.pullbackMap cospan
  square : Cone left (Over.forget k g) (FunOver k f)
  square = Cartesian.projectionSquare
  abstract
    square-isPullback : IsPullback square
    square-isPullback = Cartesian.projection-square-isPullback
    comparison : ConeIso (conePre functor (pullbackCone target named))
      (CospanMap.mapCone cospan (pullbackCone source named))
    comparison = CospanMap.pullbackMap-β cospan
```
