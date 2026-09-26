# Reassociating constant-family evaluation

A relative family uses `X × (K × S)`, whereas constant-family uncurrying uses
`(X × K) × S`. Transport the standard reassociation triangle along the
source associator and the constant-family counit. The resulting
argument retains the structure needed for evaluation over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyReassociation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Triangle; module Family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingComposition 𝒯 M ℱ P using (change-structure)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyInternalFunctors 𝒯 M ℱ P using (module ConstantFamily)

module Regroup (S : CAT) {T E K : CAT} (r : MAP E T) (k : MAP K T) (X : CAT) where
  module F = ConstantFamily S r using (constant; uncurry-constant)
  module Flat = Family r (F.constant ∘ k) X
  k′ = k ∘ pr₂ {C = X}
  A = comp-assoc (pr₂ {C = X}) k F.constant
  ζ = funUncurryIso (A ⁻¹)
  η = F.uncurry-constant k ▷ pr₂ {C = X}
  α = F.uncurry-constant k′
  initial = change-target-back ζ Flat.insertion
  middle = change-source η initial
  argument : FunctorOver ((k ∘ pr₁ {D = S}) ∘ pr₂ {C = X}) (k′ ∘ pr₁ {D = S})
  argument = change-target-back (α ⁻¹) middle

  module On (v : FunctorOver (F.constant ∘ k′) (funPost r)) where
    raw = Triangle.value r (F.constant ∘ k′) v
    changed = change-source α raw
    source = change-source η (Flat.value (change-source (A ⁻¹) v))
    target = compose-over changed argument

    abstract
      inverse-change : FunctorOverIso (change-source ((α ⁻¹) ⁻¹) raw) changed
      inverse-change = triangle-identification _ _ _
        (isoComp-cong (inverse-inverse α) (idIso (FunctorLift.comparison raw)))

      comparison : FunctorOverIso source target
      comparison = compose-iso-over (prewhisker-over argument inverse-change)
        (compose-iso-over (inverse-iso-over (Cancellation.comparison (α ⁻¹) middle raw))
          (compose-iso-over (inverse-iso-over (compose-source-change η initial raw))
            (compose-iso-over (change-source-iso η (compose-target-change ζ Flat.insertion raw))
              (change-source-iso η (prewhisker-over Flat.insertion (change-structure r (A ⁻¹) v))))))
```
