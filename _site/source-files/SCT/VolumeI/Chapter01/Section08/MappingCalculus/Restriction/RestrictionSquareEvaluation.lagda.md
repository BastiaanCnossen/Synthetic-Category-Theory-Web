# Evaluation of restriction squares

Evaluate the mapping-anima and functor-category restriction cones as
cocones on the same product square. The proved compositor comparisons
retain their matchings. Both implications of the functor-category
criterion use these comparisons; this module is independent of either proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.MapRestrictionCones as MapCones
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunRestrictionCones as FunCones
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.MapSquareEvaluation as MapEvaluation
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunSquareEvaluation as FunEvaluation
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PrecompositionComposition as MapComposition
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunPrecompositionComposition as FunComposition

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.RestrictionSquareEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M using (Map; mapUncurry)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
module MC = MapCones 𝒯 M
module FC = FunCones 𝒯 M ℱ

module Evaluated {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (E : CAT) where

  map-evaluate : {X : CAT} (h : MAP X (Map D E)) →
    CoconeIso (MC.uncurryRestriction {u = u} {v = l} (conePre h (mappingOut s E)))
      (restrictionCocone s (mapUncurry h))
  map-evaluate h = MapEvaluation.Evaluation.comparison 𝒯 M P s h
    (MapComposition.CompositorEvaluation.comparison 𝒯 M u r h)
    (MapComposition.CompositorEvaluation.comparison 𝒯 M l v h)

  fun-evaluate : {X : CAT} (h : MAP X (Fun D E)) →
    CoconeIso (FC.uncurryRestriction {u = u} {v = l} (conePre h (functorOut s E)))
      (restrictionCocone s (funUncurry h))
  fun-evaluate h = FunEvaluation.Evaluation.comparison 𝒯 M ℱ P s h
    (FunComposition.CompositorEvaluation.comparison 𝒯 M ℱ P u r h)
    (FunComposition.CompositorEvaluation.comparison 𝒯 M ℱ P l v h)

```
