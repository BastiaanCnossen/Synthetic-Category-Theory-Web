# Factoring controlled restriction comparisons

The directly reflected comparison for a restricted deformation agrees
with restriction composition, change of shape, and normalization in
succession. Agreement is proved by their specified uncurried images.
This connects the endpoint frames of the deformations with the full
restriction-corner comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationRestrictionFactorization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β; funReflect-Iso₂)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
  using (preComp; preCong; preComp-β; preCong-β)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformations as Deformations
import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles as Units

private
  abstract
    cancel-middle : {Γ C : CAT} {f g h j k : MAP Γ C}
      (α : j =₁ k) (β : h =₁ j) (γ : g =₁ h) (δ : f =₁ h) →
      ((α ∙ (β ∙ γ)) ∙ (γ ⁻¹ ∙ δ)) =₂ (α ∙ (β ∙ δ))
    cancel-middle α β γ δ = isoComp-cong (idIso α)
      (isoComp-cong (idIso β) (cancel-inverse γ δ) ∙
        isoComp-assoc-at β γ (γ ⁻¹ ∙ δ)) ∙
      isoComp-assoc-at α (β ∙ γ) (γ ⁻¹ ∙ δ)

module At (C : CAT) where
  module D = Deformations.At 𝒯 M ℱ P I E C
    using (module Deformation; module Constant)
  module U = Units.Universal 𝒯 M ℱ P I E C using (identity-evaluation; constant-evaluation)

  module Restriction (d : MAP [1] ([1] × [1])) (h : MAP ([1] × [1]) [1])
    (k : MAP [1] [1]) (α : (h ∘ d) =₁ k) where
    side : MAP (Ar C) (Ar C)
    side = funPre d ∘ funPre h
    image : funUncurry side =₁ (funEval ∘ productMap (id (Ar C)) (h ∘ d))
    image = (funEval ◁ productRestriction-comp (Ar C) d h) ∙
      (comp-assoc (productMap (id (Ar C)) d) (productMap (id (Ar C)) h) funEval ∙
        ((funPre-β h ▷ productMap (id (Ar C)) d) ∙ funPre-uncurry d (funPre h)))
    shape-image = funEval ◁ productMap-cong (idIso (id (Ar C))) α
    factor : side =₁ funPre k
    factor = preCong α ∙ preComp d h

    abstract
      factor-β : funUncurryIso factor =₂ ((funPre-β k) ⁻¹ ∙ (shape-image ∙ image))
      factor-β = cancel-middle ((funPre-β k) ⁻¹) shape-image (funPre-β (h ∘ d)) image ∙
        (isoComp-cong (preCong-β α) (preComp-β d h) ∙
          funUncurryIso-comp (preCong α) (preComp d h))

    module Normalized (F : MAP (Ar C) (Ar C)) (Z : MAP (Ar C × [1]) C)
      (β : funUncurry F =₁ Z)
      (ν : (funEval ∘ productMap (id (Ar C)) k) =₁ Z) where
      normalization : funPre k =₁ F
      normalization = funIsoReflect _ _ (β ⁻¹ ∙ (ν ∙ funPre-β k))
      direct : side =₁ F
      direct = funIsoReflect _ _ (β ⁻¹ ∙ (ν ∙ (shape-image ∙ image)))

      abstract
        direct-β : funUncurryIso direct =₂ (β ⁻¹ ∙ (ν ∙ (shape-image ∙ image)))
        direct-β = funIsoReflect-β _ _ (β ⁻¹ ∙ (ν ∙ (shape-image ∙ image)))

        comparison : (normalization ∙ factor) =₂ direct
        comparison = funReflect-Iso₂ (normalization ∙ factor) direct
          ((funIsoReflect-β _ _ (β ⁻¹ ∙ (ν ∙ (shape-image ∙ image)))) ⁻¹ ∙
            (cancel-middle (β ⁻¹) ν (funPre-β k) (shape-image ∙ image) ∙
              (isoComp-cong (funIsoReflect-β _ _ (β ⁻¹ ∙ (ν ∙ funPre-β k))) factor-β ∙
                funUncurryIso-comp normalization factor)))

  module Vertical (h : MAP ([1] × [1]) [1]) (v : Obj-abs [1]) where
    module Identity (α : (h ∘ insert v) =₁ id [1]) where
      module F = Restriction (insert v) h (id [1]) α
      module N = F.Normalized (id (Ar C)) funEval (funUncurry-id [1] C) U.identity-evaluation
      abstract
        comparison : (N.normalization ∙ F.factor) =₂ D.Deformation.Side.Identity.comparison h v α
        comparison = funReflect-Iso₂ N.direct (D.Deformation.Side.Identity.comparison h v α)
          ((D.Deformation.Side.Identity.comparison-β h v α) ⁻¹ ∙ N.direct-β) ∙ N.comparison

    module Constant (u : Obj-abs [1]) (α : (h ∘ insert v) =₁ const u) where
      module F = Restriction (insert v) h (const u) α
      module N = F.Normalized (identityArrow ∘ evaluate u) (evaluate u ∘ pr₁)
        (D.Constant.constants-uncurried u) (U.constant-evaluation u)
      abstract
        comparison : (N.normalization ∙ F.factor) =₂ D.Deformation.Side.ConstantAt.comparison h v u α
        comparison = funReflect-Iso₂ N.direct (D.Deformation.Side.ConstantAt.comparison h v u α)
          ((D.Deformation.Side.ConstantAt.comparison-β h v u α) ⁻¹ ∙ N.direct-β) ∙ N.comparison
```
