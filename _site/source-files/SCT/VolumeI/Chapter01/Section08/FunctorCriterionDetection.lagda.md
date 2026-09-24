# Detecting pushouts at the terminal parameter

Apply `Map One` to the assumed functor-category pullback. The terminal
mapping test and the evaluated restriction-square comparisons transfer
this pullback to the defining mapping-out square, retaining its matching.
Only the terminal test is used in this direction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.RestrictionTransfer as Transfer

module SCT.VolumeI.Chapter01.Section08.FunctorCriterionDetection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks 𝒯 M P
  using (map-preserves-pullback)
open import SCT.VolumeI.Chapter01.Section08.RestrictionSquareEvaluation 𝒯 M ℱ P public
  using (module Evaluated)

functor-criterion→pushout : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) → FunctorCriterion s → IsPushout s
functor-criterion→pushout s criterion E = Transfer.Detection.isPullback 𝒯 M ℱ P s E
  (Evaluated.map-evaluate s E) (Evaluated.fun-evaluate s E)
  (map-preserves-pullback One (functorOut s E) (criterion E))
```
