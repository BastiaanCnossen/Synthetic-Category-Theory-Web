# Pairing a specified change of base

The paired change of base agrees with its two endpoint comparisons.
The component squares are input data, so this calculation retains the
chosen frames rather than identifying maps only by their endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Natural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateComparisons as Coordinates

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingBaseChange
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
open Natural vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-iterated; cancel-right)
open Coordinates vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-inverse-tail)

module Along {B C D X Y : CAT} (u : MAP D X) (v : MAP D Y)
  (p : MAP C D) (q : MAP B C) {u′ : MAP C X} {v′ : MAP C Y}
  (α : (u ∘ p) =₁ u′) (β : (v ∘ p) =₁ v′)
  (δ₀ : (u ∘ (p ∘ q)) =₁ (u′ ∘ q))
  (δ₁ : (v ∘ (p ∘ q)) =₁ (v′ ∘ q))
  (source-square : (δ₀ ∙ comp-assoc q p u) =₂ (α ▷ q))
  (target-square : (δ₁ ∙ comp-assoc q p v) =₂ (β ▷ q)) where

  family-comparison : (pair u v ∘ p) =₁ pair u′ v′
  family-comparison = pair-cong α β ∙ pair-pre u v p

  base-comparison : (pair u v ∘ (p ∘ q)) =₁ (pair u′ v′ ∘ q)
  base-comparison = (family-comparison ▷ q) ∙ (comp-assoc q p (pair u v)) ⁻¹

  private
    A = comp-assoc q p (pair u v)
    A₀ = comp-assoc q p u
    A₁ = comp-assoc q p v
    P₀ = pair-pre u v p ▷ q
    P₁ = pair-pre (u ∘ p) (v ∘ p) q
    P₂ = pair-pre u v (p ∘ q)
    P′ = pair-pre u′ v′ q
    Δ = pair-cong δ₀ δ₁
    Γ = pair-cong (α ▷ q) (β ▷ q)
    κ = family-comparison ▷ q

    abstract
      component-computation : (Δ ∙ pair-cong A₀ A₁) =₂ Γ
      component-computation = pair-cong-Iso₂ source-square target-square ∙
        (pair-cong-comp δ₀ A₀ δ₁ A₁) ⁻¹

      right-computation : ((Δ ∙ P₂) ∙ A) =₂ (P′ ∙ κ)
      right-computation = isoComp-cong (idIso P′)
          ((preWhisker-isoComp-at (pair-cong α β) (pair-pre u v p) q) ⁻¹) ∙
        isoComp-assoc-at P′ (pair-cong α β ▷ q) P₀ ∙
        isoComp-cong (pair-pre-natural-inputs α β q) (idIso P₀) ∙
        (isoComp-assoc-at Γ P₁ P₀) ⁻¹ ∙
        isoComp-cong component-computation (idIso (P₁ ∙ P₀)) ∙
        (isoComp-assoc-at Δ (pair-cong A₀ A₁) (P₁ ∙ P₀)) ⁻¹ ∙
        isoComp-cong (idIso Δ) (pair-pre-iterated u v p q) ∙
        isoComp-assoc-at Δ P₂ A

      left-computation : ((P′ ∙ base-comparison) ∙ A) =₂ (P′ ∙ κ)
      left-computation = isoComp-cong (idIso P′) (cancel-inverse-tail κ A) ∙
        isoComp-assoc-at P′ (κ ∙ A ⁻¹) A

  abstract
    comparison : (P′ ∙ base-comparison) =₂ (Δ ∙ P₂)
    comparison = cancel-right A (right-computation ⁻¹ ∙ left-computation)
```
