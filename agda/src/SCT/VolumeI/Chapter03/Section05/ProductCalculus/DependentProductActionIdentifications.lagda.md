# Identifications between induced dependent-product functors

A comparison over the source base induces a comparison over the target
base. Evaluate both induced functors and reflect through currying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.DependentProductActionIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)

open import SCT.VolumeI.Chapter03.Section05.DependentProductActionLaws 𝒯 M ℱ P using (module Action)

module Identification {S T C D : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g)
  {u v : FunctorOver f g} (Φ : FunctorOverIso u v) where
  abstract
    comparison : FunctorOverIso (Induced.over p f g ΠC ΠD u) (Induced.over p f g ΠC ΠD v)
    comparison = Currying.Native.reflect p g ΠD (DependentProduct.projection ΠC) _ _
      (compose-iso-over (inverse-iso-over (Action.evaluation-comparison p f g ΠC ΠD v))
        (compose-iso-over (prewhisker-over (DependentProduct.evaluation ΠC) Φ)
          (Action.evaluation-comparison p f g ΠC ΠD u)))
```
