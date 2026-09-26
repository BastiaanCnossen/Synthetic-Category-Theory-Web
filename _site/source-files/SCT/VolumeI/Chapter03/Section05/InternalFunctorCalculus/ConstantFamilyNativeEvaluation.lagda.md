# Native evaluation for a constant source family

The constant-family comparison is evaluation on the product argument.
Transporting the uncurried triangle specifies that argument over the
base, so the computation retains more than its underlying functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyNativeEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P using (postbase)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingComposition 𝒯 M ℱ P using (module Composite)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyInternalFunctors 𝒯 M ℱ P using (module ConstantFamily)

module Evaluation (D : CAT) {E Γ : CAT} (q : MAP E Γ) {K : CAT} (k : MAP K Γ) where
  module Constant = ConstantFamily D q using (constant; projection; evaluation; uncurry-constant)
  module Native = Target Constant.constant (funPost q) k using (forward; projected; forward-normalization)
  raw = Triangle.value q (Constant.constant ∘ Constant.projection) Native.projected
  η = Constant.uncurry-constant k
  α = Constant.uncurry-constant Constant.projection

  module On (u : FunctorOver k Constant.projection) where
    original = Uncurry.value D Γ (postbase Constant.constant u)
    middle = change-source η original
    argument : FunctorOver (k ∘ pr₁ {D = D}) (Constant.projection ∘ pr₁ {D = D})
    argument = change-target-back (α ⁻¹) middle
    value = change-source η (Triangle.value q (Constant.constant ∘ k) (Native.forward u))
    module Composed = Composite q (postbase Constant.constant u) Native.projected using (comparison)
    abstract
      inverse-change : FunctorOverIso (change-source ((α ⁻¹) ⁻¹) raw) Constant.evaluation
      inverse-change = triangle-identification _ _ _
        (isoComp-cong (inverse-inverse α) (idIso (FunctorLift.comparison raw)))

      comparison : FunctorOverIso value (compose-over Constant.evaluation argument)
      comparison = compose-iso-over (prewhisker-over argument inverse-change)
        (compose-iso-over (inverse-iso-over (Cancellation.comparison (α ⁻¹) middle raw))
          (compose-iso-over (inverse-iso-over (compose-source-change η original raw))
            (change-source-iso η (compose-iso-over Composed.comparison
              (Triangle.Identification.comparison q (Constant.constant ∘ k) (Native.forward-normalization u))))))
```
