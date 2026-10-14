# Restricting a square through a coordinate

A coordinate computation for a square remains valid after changing its
parameter. Both the projection frame and the specified square matching
are retained. This packages the boundary calculation used when pairing
maps of cospans.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedSquareRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (normalize-cone-square)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯 using (coordinate-pre)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.PairedConeCoordinates 𝒯 using (normalization-restrict)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints-to-square)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (transport-pre)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones as Projected
import SCT.VolumeI.Chapter01.Section06.Coordinates.FramedProjectionRestriction as Frames

module At {C E A B A₀ B₀ : CAT}
  (F : MAP A B) (W : MAP E B) (f : MAP C E)
  (q : MAP A A₀) (π : MAP B B₀) (f₀ : MAP A₀ B₀) (w₀ : MAP E B₀)
  (ζ : (π ∘ F) =₁ (f₀ ∘ q)) (γ : (π ∘ W) =₁ w₀)
  (U : MAP C A) (u₀ : MAP C A₀) (β : (q ∘ U) =₁ u₀)
  (α : (F ∘ U) =₁ (W ∘ f)) (α₀ : (f₀ ∘ u₀) =₁ (w₀ ∘ f)) where
  private
    module Coordinate = Projected.Coordinate 𝒯 F F f₀ f₀ q q π ζ ζ using (left-normal)
    module Frame = Frames.BoundaryOnly 𝒯 π F q f₀ ζ U β using (restriction)
  square : Cone F W C
  square = record { left = U ; right = f ; match = α }
  component : Cone f₀ w₀ C
  component = record { left = u₀ ; right = f ; match = α₀ }
  left-frame = (f₀ ◁ β) ∙ Coordinate.left-normal U
  right-frame = transport-pre π W γ f
  coordinate = right-frame ∙ ((π ◁ α) ∙ left-frame ⁻¹)

  module Restrict (base-computation : coordinate =₂ α₀)
    {T : CAT} (p : MAP T C) where
    leg = transport-pre q U β p
    left-frame-at = (f₀ ◁ leg) ∙ Coordinate.left-normal (U ∘ p)
    right-frame-at = transport-pre π W γ (f ∘ p)
    projected-matching = π ◁ Cone.match (conePre p square)
    AL = comp-assoc p u₀ f₀
    AR = comp-assoc p f w₀

    abstract
      comparison :
        (Cone.match (conePre p component) ∙ left-frame-at) =₂
          (right-frame-at ∙ projected-matching)
      comparison = normalize-cone-square AL AR (α₀ ▷ p) projected-matching
        left-frame-at right-frame-at
        ((changeEndpoints-to-square left-frame-at (AR ⁻¹ ∙ right-frame-at)
            projected-matching ((α₀ ▷ p) ∙ AL ⁻¹) calculation) ⁻¹ ∙
          (isoComp-assoc-at (α₀ ▷ p) (AL ⁻¹) left-frame-at) ⁻¹)
        where
        calculation :
          ((AR ⁻¹ ∙ right-frame-at) ∙ (projected-matching ∙ left-frame-at ⁻¹)) =₂
            ((α₀ ▷ p) ∙ AL ⁻¹)
        calculation = isoComp-cong (preWhisker p ◁ base-computation) (idIso (AL ⁻¹)) ∙
          coordinate-pre π square p left-frame right-frame
            left-frame-at (AR ⁻¹ ∙ right-frame-at) (AL ⁻¹)
            (Frame.restriction p) (normalization-restrict π W w₀ γ f p)
```
