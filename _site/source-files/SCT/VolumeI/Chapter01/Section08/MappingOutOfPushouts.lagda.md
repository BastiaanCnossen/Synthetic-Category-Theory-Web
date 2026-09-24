# Mapping out of pushouts

For `prop:Mapping_Out_Of_Pushouts`, a square is a pushout precisely when
mapping from it into every functor category gives a pullback square.
Both implications use the specified matchings of the induced squares.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section08.MappingOutOfPushouts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section08.FunctorCriterionPreservation 𝒯 M ℱ P public
  using (pushout→functor-criterion)
open import SCT.VolumeI.Chapter01.Section08.FunctorCriterionDetection 𝒯 M ℱ P public
  using (functor-criterion→pushout)
```
