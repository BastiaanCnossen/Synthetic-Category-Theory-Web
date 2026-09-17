# The language used for functor categories

This module collects the derived functor-category calculus. It introduces
no assumptions beyond the preceding theory and `FunctorCategories`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.Setup
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.Currying 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.Functoriality 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.UncurryingAction 𝒯 M ℱ public
```
