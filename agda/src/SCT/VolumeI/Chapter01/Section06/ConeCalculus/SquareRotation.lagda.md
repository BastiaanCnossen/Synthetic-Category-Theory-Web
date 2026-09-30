# Rotating an evaluated cone comparison

This identity moves a comparison between two evaluated cone matchings
into the comparison needed for the transverse faces. All six edge
identifications remain specified; the proof only uses associativity and
inverse cancellation in the mapping anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.SquareRotation
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-left)

abstract
  rotate : {X Y : CAT} {a₀ a₁ b₀ b₁ c₀ c₁ : MAP X Y}
    (δ : a₀ =₁ a₁) (Ω : a₀ =₁ b₀) (γ : b₀ =₁ b₁)
    (β : b₁ =₁ c₁) (ω : c₀ =₁ c₁) (α : a₁ =₁ c₀) →
    (ω ∙ α) =₂ (β ∙ (γ ∙ (Ω ∙ δ ⁻¹))) →
    (δ ∙ Ω ⁻¹) =₂ (α ⁻¹ ∙ (ω ⁻¹ ∙ (β ∙ γ)))
  rotate δ Ω γ β ω α given =
    (cancel-left α (δ ∙ Ω ⁻¹) ∙
      (isoComp-cong (idIso (α ⁻¹)) (isoComp-assoc-at α δ (Ω ⁻¹)) ∙
        isoComp-cong (idIso (α ⁻¹)) (move-square ω (α ∙ δ) (β ∙ γ) Ω grouped))) ⁻¹
    where
    regroup : (β ∙ (γ ∙ (Ω ∙ δ ⁻¹))) =₂ (((β ∙ γ) ∙ Ω) ∙ δ ⁻¹)
    regroup = (isoComp-assoc-at (β ∙ γ) Ω (δ ⁻¹)) ⁻¹ ∙
      (isoComp-assoc-at β γ (Ω ∙ δ ⁻¹)) ⁻¹
    grouped : (ω ∙ (α ∙ δ)) =₂ ((β ∙ γ) ∙ Ω)
    grouped = isoComp-unitʳ-at ((β ∙ γ) ∙ Ω) ∙
      (isoComp-cong (idIso ((β ∙ γ) ∙ Ω)) (isoComp-inverseˡ-at δ) ∙
      (isoComp-assoc-at ((β ∙ γ) ∙ Ω) (δ ⁻¹) δ ∙
      (isoComp-cong (regroup ∙ given) (idIso δ) ∙
        (isoComp-assoc-at ω α δ) ⁻¹)))
```
