# Evaluation of the base-change constructor

The generic projection calculation applies to the stipulated universal
family defining base change. Thus projection after base change agrees
with restriction along the source pullback projection, as a family over
the original base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.EvaluatedBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeFamilyProjection 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)

module Evaluation {C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T) where
  module Projected = Change p f g
  module Actual = BaseChange p f g
  X = FunOver f g

  pulled-family : FunctorOver (Projected.f′ ∘ pr₂ {C = X}) Projected.g′
  pulled-family = Projected.At.pulled {X = X} (universal f g)

  abstract
    same-family : FunctorOverIso Actual.evaluated pulled-family
    same-family = identity-iso-over Actual.evaluated

    generic-projection : FunctorOverIso
      (Projected.Project.forward {X = X} pulled-family)
      (compose-over (universal f g) (Projected.Arg.family X))
    generic-projection = Projected.At.projection-comparison {X = X} (universal f g)

    projection-comparison : FunctorOverIso
      (Projected.Project.forward {X = X} Actual.evaluated)
      (compose-over (universal f g) (Projected.Arg.family X))
    projection-comparison = compose-iso-over generic-projection
      (Projected.Project.forward-identification same-family)
```
