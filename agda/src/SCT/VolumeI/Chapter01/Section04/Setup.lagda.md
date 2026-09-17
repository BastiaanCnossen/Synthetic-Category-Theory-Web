# The language used for initial categories and coproducts

We keep the mapping-anima interface as a separate parameter. This module
only collects previously proved operations; it introduces no assumptions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section04.Setup
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯 public
open Mapping.MappingAnimae M public
open import SCT.VolumeI.Chapter01.Section03.Currying 𝒯 M public
open import SCT.VolumeI.Chapter01.Section03.Points 𝒯 M public
open import SCT.VolumeI.Chapter01.Section03.Functoriality 𝒯 M public
open import SCT.VolumeI.Chapter01.Section03.EquivalenceDetection 𝒯 M public
  using (unnamedIso; mapPre-name; mapPost-name)
```
