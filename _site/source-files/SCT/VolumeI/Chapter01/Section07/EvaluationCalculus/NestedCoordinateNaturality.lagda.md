# Naturality of a nested coordinate

An identified parameter commutes with associating a composite of two
functors. Both the nested and distributed coordinate frames are retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.NestedCoordinateNaturality
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)

module At {Γ Δ B C D : CAT} (s : MAP Δ Γ) (x : MAP Γ B) {y : MAP Δ B}
  (ξ : (x ∘ s) =₁ y) (g : MAP B C) (h : MAP C D) where
  θ = comp-assoc x g h
  κ = comp-assoc y g h
  image-frame = h ◁ (g ◁ ξ)
  inner-assoc = h ◁ comp-assoc s x g
  outer-assoc = comp-assoc s (g ∘ x) h
  nested = (h ◁ ((g ◁ ξ) ∙ comp-assoc s x g)) ∙ outer-assoc
  distributed = image-frame ∙ (inner-assoc ∙ outer-assoc)
  composite = ((h ∘ g) ◁ ξ) ∙ comp-assoc s x (h ∘ g)

  abstract
    normalization : nested =₂ distributed
    normalization = isoComp-assoc-at image-frame inner-assoc outer-assoc ∙
      isoComp-cong (postWhisker-isoComp-at h (g ◁ ξ) (comp-assoc s x g)) (idIso outer-assoc)

    square : (distributed ∙ (θ ▷ s)) =₂ (κ ∙ composite)
    square = isoComp-assoc-at κ ((h ∘ g) ◁ ξ) (comp-assoc s x (h ∘ g)) ∙
      isoComp-cong ((postWhisker-comp-at ξ g h) ⁻¹) (idIso (comp-assoc s x (h ∘ g))) ∙
      (isoComp-assoc-at image-frame (comp-assoc (x ∘ s) g h) (comp-assoc s x (h ∘ g))) ⁻¹ ∙
      isoComp-cong (idIso image-frame) ((pentagon-whiskered s x g h) ⁻¹) ∙
      isoComp-cong (idIso image-frame) (isoComp-assoc-at inner-assoc outer-assoc (θ ▷ s)) ∙
      isoComp-assoc-at image-frame (inner-assoc ∙ outer-assoc) (θ ▷ s)

    nested-square : (nested ∙ (θ ▷ s)) =₂ (κ ∙ composite)
    nested-square = square ∙ isoComp-cong normalization (idIso (θ ▷ s))
```
