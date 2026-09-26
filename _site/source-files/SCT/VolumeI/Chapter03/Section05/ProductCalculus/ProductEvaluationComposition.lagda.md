# Uncurrying a functor into the dependent-product candidate

Projection from the defining pullback is composition with its universal
triangle. Uncurrying carries that composite to product evaluation after
the product of the original functor with the identity. The comparison
includes the structure triangle over the product base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductEvaluationComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (change-middle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P using (postbase)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingComposition 𝒯 M ℱ P using (module Composite)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductDependentEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductUncurryingTriangles 𝒯 M ℱ P using (module Product)

module CompositeEvaluation {T S E K : CAT} (r : MAP E (T × S))
  (k : MAP K T) (u : FunctorOver k (Evaluation.projection r)) where
  module Ev = Evaluation r
  module Native = Target Ev.F.name (funPost r) k
  module U = Product S u
  source = change-source (Ev.F.uncurry-name k)
    (Triangle.value r (Ev.F.name ∘ k) (Native.forward u))
  target = compose-over Ev.product-evaluation U.value
  projected = Native.projected
  raw-evaluation = Triangle.value r (Ev.F.name ∘ Ev.projection) projected

  abstract
    change-comparison : FunctorOverIso
      (change-source (Ev.F.uncurry-name k) (compose-over raw-evaluation U.U.original)) target
    change-comparison = triangle-identification _ _ _
      ((change-middle r (FunctorLift.lift raw-evaluation) U.U.H
        (FunctorLift.comparison raw-evaluation) (FunctorLift.comparison U.U.original)
        (Ev.F.uncurry-name Ev.projection) U.triangle (Ev.F.uncurry-name k) U.comparison) ⁻¹)

    comparison : FunctorOverIso source target
    comparison = compose-iso-over change-comparison
      (compose-iso-over
        (change-source-iso (Ev.F.uncurry-name k)
          (Composite.comparison r (postbase Ev.F.name u) projected))
        (change-source-iso (Ev.F.uncurry-name k)
          (Triangle.Identification.comparison r (Ev.F.name ∘ k) (Native.forward-normalization u))))
```
