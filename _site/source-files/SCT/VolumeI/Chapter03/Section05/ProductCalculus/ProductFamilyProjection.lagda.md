# The projection after fiberwise reassociation

The reassociated parameter argument has the expected projection over
the product base. Prove this before identifying it with a pullback
parameter: the calculation cancels the two changes of source structure
and then uses the projection rule for uncurried families.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductFamilyProjection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TriangleTransport 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.TargetChangeIdentifications 𝒯 M ℱ P using (reflect-target-change) renaming (module Composite to TargetComposite)
open import SCT.VolumeI.Chapter03.Section05.Currying.FamilyProjection 𝒯 M ℱ P using (projection)
open import SCT.VolumeI.Chapter03.Section05.Currying.UncurriedFamilyProjection 𝒯 M ℱ P using (module Project)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductUncurryingTriangles 𝒯 M ℱ P using (module Product)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.ProductFamilyReassociation 𝒯 M ℱ P using (module Regroup)

module Projection {T S E K : CAT} (r : MAP E (T × S)) (k : MAP K T) (X : CAT) where
  module R = Regroup r k X
  module L = Product S (projection k X)
  module U = Project r (R.F.name ∘ k) X
  α = R.F.uncurry-name k
  raw = L.U.original
  q = U.q
  A = R.A
  μ = funUncurryIso A
  ν = L.U.ν
  source = compose-over L.value R.argument
  target = projection (productMap k (id S)) X

  abstract
    original-normal : FunctorLift.comparison raw =₂ (μ ∙ ν ⁻¹)
    original-normal = isoComp-cong
      (funUncurry-isoMap _ _ ◁
        (isoComp-unitˡ-at A ∙ isoComp-cong (postWhisker-idIso R.F.name R.k′) (idIso A)))
      (idIso (ν ⁻¹))

    inverse-source : (R.ζ ⁻¹) =₂ μ
    inverse-source = inverse-inverse μ ∙ (＝-inv ◁ funUncurryIso-inverse A)

    projection-normal : FunctorLift.comparison (change-source (R.ζ ⁻¹) q) =₂ (μ ∙ ν ⁻¹)
    projection-normal = isoComp-cong inverse-source
      (isoComp-unitˡ-at (ν ⁻¹) ∙ isoComp-cong (funUncurryIso-id ((R.F.name ∘ k) ∘ pr₂)) (idIso (ν ⁻¹)))

    raw-projection : FunctorOverIso raw (change-source (R.ζ ⁻¹) q)
    raw-projection = triangle-identification _ _ _ (projection-normal ⁻¹ ∙ original-normal)

    product-normal : FunctorOverIso (change-target-back α L.value) (change-source R.α raw)
    product-normal = triangle-identification _ _ _ (L.comparison ⁻¹)

    inverse-change : FunctorOverIso (change-source R.α raw) (change-source ((R.α ⁻¹) ⁻¹) raw)
    inverse-change = triangle-identification _ _ _
      (isoComp-cong ((inverse-inverse R.α) ⁻¹) (idIso (FunctorLift.comparison raw)))

    final-projection : FunctorOverIso (change-source R.η U.target) (change-target-back α target)
    final-projection = triangle-identification _ _ _
      ((isoComp-unitˡ-at R.η) ⁻¹ ∙ isoComp-unitʳ-at R.η)

    changed-comparison : FunctorOverIso (change-target-back α source) (change-target-back α target)
    changed-comparison = compose-iso-over final-projection
      (compose-iso-over (change-source-iso R.η U.comparison)
        (compose-iso-over (change-source-iso R.η (Cancellation.comparison R.ζ R.Flat.insertion q))
          (compose-iso-over (change-source-iso R.η (prewhisker-over R.initial raw-projection))
            (compose-iso-over (compose-source-change R.η R.initial raw)
              (compose-iso-over (Cancellation.comparison (R.α ⁻¹) R.middle raw)
                (compose-iso-over (prewhisker-over R.argument inverse-change)
                  (compose-iso-over (prewhisker-over R.argument product-normal)
                    (TargetComposite.comparison α R.argument L.value))))))))

    comparison : FunctorOverIso source target
    comparison = reflect-target-change α changed-comparison
```
