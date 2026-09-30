# Unit laws for product substitution

The product substitution comparison includes a normalization of the
identity on the fixed coordinate. Its left and right unit laws therefore
retain that normalization explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitutionUnits
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SectionFrames 𝒯 using (identity-unitors)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (productMap-unitˡ; productMap-unitʳ)

module At {X Y : CAT} (K : CAT) (h : MAP X Y) where
  π : MAP (X × K) (Y × K)
  π = productMap h (id K)

  private
    merge : {f g : MAP X Y} (p : f =₁ g) →
      (productMap-cong p (idIso (id K)) ∙ productMap-cong (idIso f) (comp-unitˡ (id K))) =₂
      productMap-cong p (comp-unitˡ (id K))
    merge p = productMap-cong-Iso₂ (isoComp-unitʳ-at p) (isoComp-unitˡ-at (comp-unitˡ (id K))) ∙
      (productMap-cong-comp p (idIso _) (idIso (id K)) (comp-unitˡ (id K))) ⁻¹

  abstract
    left : (productMap-cong (comp-unitˡ h) (idIso (id K)) ∙ slice-comparison (id Y) h) =₂
      (comp-unitˡ π ∙ (productMap-id Y K ▷ π))
    left = productMap-unitˡ h (id K) ∙
      isoComp-cong (merge (comp-unitˡ h)) (idIso (productMap-comp h (id Y) (id K) (id K))) ∙
      (isoComp-assoc-at (productMap-cong (comp-unitˡ h) (idIso (id K)))
        (productMap-cong (idIso (id Y ∘ h)) (comp-unitˡ (id K)))
        (productMap-comp h (id Y) (id K) (id K))) ⁻¹

    right : (productMap-cong (comp-unitʳ h) (idIso (id K)) ∙ slice-comparison h (id X)) =₂
      (comp-unitʳ π ∙ (π ◁ productMap-id X K))
    right = productMap-unitʳ h (id K) ∙
      isoComp-cong (productMap-cong-Iso₂ (idIso (comp-unitʳ h)) ((identity-unitors K) ⁻¹) ∙
        merge (comp-unitʳ h)) (idIso (productMap-comp (id X) h (id K) (id K))) ∙
      (isoComp-assoc-at (productMap-cong (comp-unitʳ h) (idIso (id K)))
        (productMap-cong (idIso (h ∘ id X)) (comp-unitˡ (id K)))
        (productMap-comp (id X) h (id K) (id K))) ⁻¹
```
