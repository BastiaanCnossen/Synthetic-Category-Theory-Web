# Evaluation of the constant-family comparison

The equivalence for a constant source family acts by evaluation. Project
a family to the ordinary functor category, uncurry it, and change its
structure using the constant-family computation. The comparison below
retains the base triangle. Its underlying formula is precisely the
evaluation functor composed with the family times `D`, after reassociating
the parameter product.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ConstantFamilyEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family; family-identification)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (change-source; change-source-iso)
open import SCT.VolumeI.Chapter03.Section05.Currying.SourceChangeFamilies 𝒯 M ℱ P using (module Source)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Family)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyInternalFunctors 𝒯 M ℱ P using (module ConstantFamily)
import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyNativeEvaluation as NativeEvaluation
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyReassociation 𝒯 M ℱ P using (module Regroup)

module Evaluation (D : CAT) {E Γ : CAT} (q : MAP E Γ) {K : CAT} (k : MAP K Γ) where
  module Constant = ConstantFamily D q
  module At = Constant.At k
  module Structure = Source (Constant.uncurry-constant k) q
  SourceCategory = FunOver k Constant.projection
  module Parameters (X : CAT) where
    module Uncurried = Family q (Constant.constant ∘ k) X
    value : FunctorOver (k ∘ pr₂ {C = X}) Constant.projection →
      FunctorOver ((k ∘ pr₁ {D = D}) ∘ pr₂ {C = X}) q
    value u = change-source (Constant.uncurry-constant k ▷ pr₂)
      (Uncurried.value (At.Target.Native.forward u))
    abstract
      comparison : (F : MAP X SourceCategory) →
        FunctorOverIso (family (k ∘ pr₁ {D = D}) q (At.functor ∘ F)) (value (family k Constant.projection F))
      comparison F = compose-iso-over
        (change-source-iso (Constant.uncurry-constant k ▷ pr₂)
          (compose-iso-over (Uncurried.identification (At.Target.family-comparison F))
            (At.Exponential.family-comparison (At.Target.functor ∘ F))))
        (compose-iso-over (Structure.substituted-comparison (At.Exponential.functor ∘ (At.Target.functor ∘ F)))
          (family-identification _ q
            ((At.Structure.functor ◁ comp-assoc F At.Target.functor At.Exponential.functor) ∙
              comp-assoc F (At.Exponential.functor ∘ At.Target.functor) At.Structure.functor)))

      underlying-evaluation : (u : FunctorOver (k ∘ pr₂ {C = X}) Constant.projection) →
        FunctorLift.lift (value u) =₁
        (FunctorLift.lift Constant.evaluation ∘
          (productMap (FunctorLift.lift u) (id D) ∘ Uncurried.regroup))
      underlying-evaluation u = comp-assoc Uncurried.regroup (productMap (FunctorLift.lift u) (id D))
        (FunctorLift.lift Constant.evaluation) ∙
        (funUncurry-restrict Constant.sections (FunctorLift.lift u) ▷ Uncurried.regroup)

    module Regrouped = Regroup D q k X using (argument; module On)
    module Native = NativeEvaluation.Evaluation 𝒯 M ℱ P D q (k ∘ pr₂ {C = X}) using (module On; module Native)

    argument : FunctorOver (k ∘ pr₂ {C = X}) Constant.projection →
      FunctorOver ((k ∘ pr₁ {D = D}) ∘ pr₂ {C = X}) (Constant.projection ∘ pr₁ {D = D})
    argument u = compose-over (Native.On.argument u) Regrouped.argument

    abstract
      argument-underlying : (u : FunctorOver (k ∘ pr₂ {C = X}) Constant.projection) →
        FunctorLift.lift (argument u) =₁
          (productMap (FunctorLift.lift u) (id D) ∘ Uncurried.regroup)
      argument-underlying u = idIso _

      native-evaluation : (u : FunctorOver (k ∘ pr₂ {C = X}) Constant.projection) →
        FunctorOverIso (value u) (compose-over Constant.evaluation (argument u))
      native-evaluation u = compose-iso-over
        (associator-over Regrouped.argument (Native.On.argument u) Constant.evaluation)
        (compose-iso-over (prewhisker-over Regrouped.argument (Native.On.comparison u))
          (Regrouped.On.comparison (Native.Native.forward u)))

      evaluation-comparison : (F : MAP X SourceCategory) →
        FunctorOverIso (family (k ∘ pr₁ {D = D}) q (At.functor ∘ F))
          (compose-over Constant.evaluation (argument (family k Constant.projection F)))
      evaluation-comparison F = compose-iso-over
        (native-evaluation (family k Constant.projection F)) (comparison F)
```
