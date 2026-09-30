# Evaluation commutes with induced dependent-product functors

The defining evaluation comparison for an induced functor can be
restricted along any functor over the new base. The composition rule
for native uncurrying and the relative associator give the resulting
naturality identification, including its base triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.DependentProductEvaluationNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.Section05.DependentProductActionLaws 𝒯 M ℱ P using (module Action)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)

module Naturality {S T C D : CAT} (p : MAP S T) (f : MAP C S) (g : MAP D S)
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (u : FunctorOver f g) where
  module Source = Currying p f ΠC
  module Target = Currying p g ΠD
  induced = Induced.over p f g ΠC ΠD u
  abstract
    comparison : {K : CAT} {k : MAP K T} (w : FunctorOver k (DependentProduct.projection ΠC)) →
      FunctorOverIso (Target.evaluate (compose-over induced w)) (compose-over u (Source.evaluate w))
    comparison w = compose-iso-over (associator-over (Change.functor p w) (DependentProduct.evaluation ΠC) u)
      (compose-iso-over (prewhisker-over (Change.functor p w)
        (Action.evaluation-comparison p f g ΠC ΠD u))
        (Target.Native.evaluate-composite w induced))
```
