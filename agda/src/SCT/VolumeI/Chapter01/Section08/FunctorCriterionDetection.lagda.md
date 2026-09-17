# Detecting pushouts by functor categories

For the reverse implication of `prop:Mapping_Out_Of_Pushouts`, evaluate
both restriction cones as cocones on the same product square. The proved
compositor comparisons retain their matchings. The lifting argument can
therefore pass through functor categories and return to mapping animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.MapRestrictionCones as MapCones
import SCT.VolumeI.Chapter01.Section08.FunRestrictionCones as FunCones
import SCT.VolumeI.Chapter01.Section08.MapSquareEvaluation as MapEvaluation
import SCT.VolumeI.Chapter01.Section08.FunSquareEvaluation as FunEvaluation
import SCT.VolumeI.Chapter01.Section08.PrecompositionComposition as MapComposition
import SCT.VolumeI.Chapter01.Section08.FunPrecompositionComposition as FunComposition
import SCT.VolumeI.Chapter01.Section08.RestrictionTransfer as Transfer

module SCT.VolumeI.Chapter01.Section08.FunctorCriterionDetection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M using (Map; mapUncurry)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeRestriction 𝒯
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

functor-criterion→pushout : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) → FunctorCriterion s → IsPushout s
functor-criterion→pushout s criterion E = Transfer.Detection.isPullback 𝒯 M ℱ P s E
  (Evaluated.map-evaluate s E) (Evaluated.fun-evaluate s E) (criterion E)
```
