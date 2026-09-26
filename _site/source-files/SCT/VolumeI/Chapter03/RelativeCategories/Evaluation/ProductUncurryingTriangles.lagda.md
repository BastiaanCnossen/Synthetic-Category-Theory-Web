# The triangle of fiberwise uncurrying

Specialize uncurrying to the family of fibers of a product projection.
The counit of currying identifies its uncurrying with the identity.
Naturality of that single identification gives the ordinary product
triangle, retaining the changes of source and target structure.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductUncurryingTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (lift-base)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedBaseTriangles 𝒯 M ℱ P using (module Triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductDependentEvaluation 𝒯 M ℱ P using (module Fibers)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.BaseIdentityTriangles 𝒯 using (module Change)

module Product {K G T : CAT} (S : CAT) {k : MAP K T} {g : MAP G T}
  (u : FunctorOver k g) where
  module F = Fibers T S
  module U = Triangle F.name u
  module Identity = Change (funCurry-β (id (T × S)))
  triangle = U.τ ∙ U.κ
  value : FunctorOver U.K′ U.G′
  value = record { lift = U.H ; comparison = triangle }

  abstract
    normalize : U.triangle =₂ lift-base (funUncurry F.name) U.G′ U.H triangle
    normalize = isoComp-cong ((postWhisker-isoComp-at (funUncurry F.name) U.τ U.κ) ⁻¹) (idIso U.A′)

    comparison : (F.uncurry-name k ∙ FunctorLift.comparison U.original) =₂
      (triangle ∙ (F.uncurry-name g ▷ U.H))
    comparison = isoComp-cong (idIso triangle)
        ((preWhisker-isoComp-at (Identity.structure U.G′) U.α U.H) ⁻¹) ∙
      (isoComp-assoc-at triangle (Identity.structure U.G′ ▷ U.H) U.δ ∙
        (isoComp-cong
          (Identity.comparison U.G′ U.H U.K′ triangle ∙
            isoComp-cong (idIso (Identity.structure U.K′)) normalize)
          (idIso U.δ) ∙
          ((isoComp-assoc-at (Identity.structure U.K′) U.triangle U.δ) ⁻¹ ∙
            (isoComp-cong (idIso (Identity.structure U.K′)) U.comparison ∙
              isoComp-assoc-at (Identity.structure U.K′) U.η (FunctorLift.comparison U.original)))))
```
