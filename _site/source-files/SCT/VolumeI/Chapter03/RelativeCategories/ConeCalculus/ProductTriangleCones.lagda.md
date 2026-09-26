# Product triangles as comparisons of pullback cones

A triangle over `T` gives a comparison between the corresponding
product cones. The right leg is exactly the product triangle used by
fiberwise uncurrying. Its compatibility follows by projecting the
chosen product composition comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ProductTriangleCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module FirstFactor)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; inverse-inverse; pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductComparisonProjections 𝒯 using (module Normalized)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ProductUncurryingTriangles 𝒯 M ℱ P using (module Product)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module Triangle {K G T : CAT} (S : CAT) {k : MAP K T} {g : MAP G T} (u : FunctorOver k g) where
  module V = Product S u
  h = FunctorLift.lift u
  θ = FunctorLift.comparison u
  H = productMap h (id S)
  module N = Normalized h g (id S) (id S) θ (comp-unitˡ (id S))
  b = pair-β₁ (k ∘ pr₁) (id S ∘ pr₂)
  bg = pair-β₁ (g ∘ pr₁) (id S ∘ pr₂)
  bh = pair-β₁ (h ∘ pr₁) (id S ∘ pr₂)
  A = comp-assoc H (productMap g (id S)) (pr₁ {T} {S})
  B′ = comp-assoc H (pr₁ {G} {S}) g
  C′ = comp-assoc (pr₁ {K} {S}) h g
  ψ = θ ▷ pr₁ {K} {S}
  χ = g ◁ bh
  d = bg ▷ H
  tail = B′ ∙ (d ∙ A ⁻¹)
  e = (ψ ∙ C′ ⁻¹) ∙ χ
  source = conePre H (FirstFactor.square g S)
  target : Cone g (pr₁ {T} {S}) (K × S)
  target = record { left = h ∘ pr₁ ; right = productMap k (id S)
    ; match = b ⁻¹ ∙ (ψ ∙ C′ ⁻¹) }

  abstract
    normalization : V.triangle =₂ N.value
    normalization = isoComp-cong
      (productMap-cong-Iso₂ (isoComp-unitʳ-at θ) (isoComp-unitˡ-at (comp-unitˡ (id S))) ∙
        (productMap-cong-comp θ (idIso (g ∘ h)) (idIso (id S)) (comp-unitˡ (id S))) ⁻¹)
      (idIso (productMap-comp h g (id S) (id S))) ∙
      (isoComp-assoc-at V.U.τ (productMap-cong (idIso (g ∘ h)) (comp-unitˡ (id S)))
        (productMap-comp h g (id S) (id S))) ⁻¹

    projected : (b ∙ (pr₁ ◁ V.triangle)) =₂ (e ∙ tail)
    projected = isoComp-assoc-at e B′ (d ∙ A ⁻¹) ∙
      (isoComp-cong ((isoComp-assoc-at (ψ ∙ C′ ⁻¹) χ B′) ⁻¹) (idIso (d ∙ A ⁻¹)) ∙
        (isoComp-cong ((isoComp-assoc-at ψ (C′ ⁻¹) (χ ∙ B′)) ⁻¹) (idIso (d ∙ A ⁻¹)) ∙
          (N.projection₁ ∙ isoComp-cong (idIso b) (postWhisker pr₁ ◁ normalization))))

    inverse-tail : (tail ⁻¹) =₂ Cone.match source
    inverse-tail = isoComp-cong (idIso A)
      (isoComp-cong ((pre-inverse bg H) ⁻¹) (idIso (B′ ⁻¹))) ∙
      (isoComp-assoc-at A (d ⁻¹) (B′ ⁻¹) ∙
        (isoComp-cong (isoComp-cong (inverse-inverse A) (idIso (d ⁻¹)) ∙ inverse-composite d (A ⁻¹))
          (idIso (B′ ⁻¹)) ∙ inverse-composite B′ (d ∙ A ⁻¹)))

    comparison : ConeIso source target
    comparison = record { leftIso = bh ; rightIso = V.triangle
      ; compatible = isoComp-cong (idIso (pr₁ ◁ V.triangle)) inverse-tail ∙
          (move-square b (pr₁ ◁ V.triangle) e tail projected ∙
            isoComp-assoc-at (b ⁻¹) (ψ ∙ C′ ⁻¹) χ) }

    right-image : ConeIso.rightIso comparison =₂ V.triangle
    right-image = idIso _
```
