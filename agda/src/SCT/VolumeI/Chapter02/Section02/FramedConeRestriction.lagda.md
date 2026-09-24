# Restricting a cone specified by endpoint frames

Restrict both legs and both frames together. The resulting quotient of
frames is the specified restricted matching. A comparison of whole cones
therefore restricts with the expected two edge comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.FramedConeRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯
import SCT.VolumeI.Chapter02.Section02.TransposedEndpointFrames as Frames
open Frames.FrameCalculus 𝒯 M ℱ P using (quotient-pre; quotient-common)

framed-cone : {Γ A B C : CAT} {f : MAP A C} {g : MAP B C}
  (p : MAP Γ A) (q : MAP Γ B) {z : MAP Γ C} →
  (f ∘ p) =₁ z → (g ∘ q) =₁ z → Cone f g Γ
framed-cone p q α β = record { left = p ; right = q ; match = β ⁻¹ ∙ α }

module Restrict {Γ Δ A B C : CAT} {f : MAP A C} {g : MAP B C}
  (p : MAP Γ A) (q : MAP Γ B) {z : MAP Γ C}
  (α : (f ∘ p) =₁ z) (β : (g ∘ q) =₁ z) (r : MAP Δ Γ) where
  left-associator = comp-assoc r p f
  right-associator = comp-assoc r q g
  left-frame = (α ▷ r) ∙ left-associator ⁻¹
  right-frame = (β ▷ r) ∙ right-associator ⁻¹
  source = conePre r (framed-cone p q α β)
  target = framed-cone (p ∘ r) (q ∘ r) left-frame right-frame

  abstract
    quotient-image : ((β ⁻¹ ∙ α) ▷ r) =₂ ((β ▷ r) ⁻¹ ∙ (α ▷ r))
    quotient-image = isoComp-cong (pre-inverse β r) (idIso (α ▷ r)) ∙
      preWhisker-isoComp-at (β ⁻¹) α r

    matching : Cone.match source =₂ Cone.match target
    matching =
      (quotient-pre (α ▷ r) (β ▷ r) (left-associator ⁻¹) (right-associator ⁻¹)) ⁻¹ ∙
      isoComp-cong ((inverse-inverse right-associator) ⁻¹)
        (isoComp-cong quotient-image (idIso (left-associator ⁻¹)))

  comparison : ConeIso source target
  comparison = cone-match-change (p ∘ r) (q ∘ r) _ _ matching

module RestrictComparison {Γ Δ T A B C : CAT} {f : MAP A C} {g : MAP B C}
  (s : Cone f g T) (σ : MAP Γ T) (r : MAP Δ Γ)
  (p : MAP Γ A) (q : MAP Γ B) {z : MAP Γ C}
  (α : (f ∘ p) =₁ z) (β : (g ∘ q) =₁ z)
  (Φ : ConeIso (conePre σ s) (framed-cone p q α β)) where
  module R = Restrict p q α β r
  left-edge = (ConeIso.leftIso Φ ▷ r) ∙ (comp-assoc r σ (Cone.left s)) ⁻¹
  right-edge = (ConeIso.rightIso Φ ▷ r) ∙ (comp-assoc r σ (Cone.right s)) ⁻¹
  together = coneIso-compose (coneIso-pre r Φ) (coneIso-inverse (conePre-assoc r σ s))
  raw = coneIso-compose R.comparison together

  comparison : ConeIso (conePre (σ ∘ r) s) R.target
  comparison = coneIso-adjust raw left-edge right-edge
    (isoComp-unitˡ-at left-edge) (isoComp-unitˡ-at right-edge)
```
