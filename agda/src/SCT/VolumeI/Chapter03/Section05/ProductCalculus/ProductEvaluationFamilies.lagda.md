# Fiberwise evaluation on an entire relative family

The pullback-target and exponential comparisons, followed by the
change of source structure, evaluate a family by product evaluation.
The reassociation is shared by the whole family and its triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductEvaluationFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target)
open import SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductDependentEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductUncurryingTriangles 𝒯 M ℱ P using (module Product)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductEvaluationComposition 𝒯 M ℱ P using (module CompositeEvaluation)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductFamilyReassociation 𝒯 M ℱ P using (module Regroup)

module Evaluate {T S E K X : CAT} (r : MAP E (T × S)) (k : MAP K T)
  (u : FunctorOver (k ∘ pr₂ {C = X}) (Evaluation.projection r)) where
  module Ev = Evaluation r
  module R = Regroup r k X
  module N = Target Ev.F.name (funPost r) R.k′
  module C = CompositeEvaluation r R.k′ u
  argument = compose-over (Product.value S u) R.argument
  source = change-source R.η (R.Flat.value (Families.forward Ev.F.name (funPost r) k u))
  target = compose-over Ev.product-evaluation argument

  abstract
    comparison : FunctorOverIso source target
    comparison = compose-iso-over (associator-over R.argument (Product.value S u) Ev.product-evaluation)
      (compose-iso-over (prewhisker-over R.argument C.comparison) (R.On.comparison (N.forward u)))
```
