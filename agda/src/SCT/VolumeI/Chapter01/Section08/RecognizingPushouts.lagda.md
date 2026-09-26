# Recognizing a pushout by extension and comparison

Ordinary cocones suffice when tested at every target category: the
functor-category targets supply the parameter categories needed by the
mapping-out criterion.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section08.RecognizingPushouts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 using (squareCocone)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorCriterionPreservation 𝒯 M ℱ P using (module Preservation)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorCriterionDetection 𝒯 M ℱ P using (functor-criterion→pushout)

cocone-extension→pushout : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) → CoconeExtensionProperty (squareCocone s) → IsPushout s
cocone-extension→pushout s extensions =
  functor-criterion→pushout s (Preservation.isPullback s extensions)
```
