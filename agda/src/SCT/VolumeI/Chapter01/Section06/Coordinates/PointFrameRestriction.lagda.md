# Restricting a frame at an absolute point

A projected point frame can be restricted along a generalized point of
the terminal category. Its resulting comparison is the projected
restricted frame. The proof retains the triangle and associator laws.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.Coordinates.PointFrameRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯
  using (restricted-normalization; normalization-pre)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯
  using (lift-base; lift-compose; compose-base)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)

module At {X Y Z : CAT} (π : MAP Y Z) (H : MAP X Y) (q : MAP X One)
  (f : MAP One Z) (ζ : (π ∘ H) =₁ (f ∘ q)) (h : MAP One X)
  (ε : (q ∘ h) =₁ id One) where

  projected : (π ∘ (H ∘ h)) =₁ (f ∘ (q ∘ h))
  projected = comp-assoc h q f ∙ transport-pre π H ζ h

  frame : (π ∘ (H ∘ h)) =₁ f
  frame = comp-unitʳ f ∙ ((f ◁ ε) ∙ projected)

  n : ((f ∘ q) ∘ h) =₁ f
  n = comp-unitʳ f ∙ lift-base f q h ε

  abstract
    frame-normal : frame =₂ (n ∙ transport-pre π H ζ h)
    frame-normal = (isoComp-assoc-at (comp-unitʳ f) (lift-base f q h ε)
      (transport-pre π H ζ h)) ⁻¹ ∙
      isoComp-cong (idIso (comp-unitʳ f))
        ((isoComp-assoc-at (f ◁ ε) (comp-assoc h q f) (transport-pre π H ζ h)) ⁻¹)

  module Restrict {Γ : CAT} (t : MAP Γ One) where
    point-frame : (q ∘ (h ∘ t)) =₁ t
    point-frame = comp-unitˡ t ∙ transport-pre q h ε t

    projected-at : (π ∘ (H ∘ (h ∘ t))) =₁ (f ∘ (q ∘ (h ∘ t)))
    projected-at = comp-assoc (h ∘ t) q f ∙ transport-pre π H ζ (h ∘ t)

    abstract
      outer-normal : transport-pre (f ∘ q) h n t =₂
        lift-base f q (h ∘ t) point-frame
      outer-normal = lift-compose f q h t ε (comp-unitˡ t) ∙
        (isoComp-cong (triangle-whiskered t f)
          (idIso (transport-pre (f ∘ q) h (lift-base f q h ε) t)) ∙
        (isoComp-assoc-at (comp-unitʳ f ▷ t) (lift-base f q h ε ▷ t)
          ((comp-assoc t h (f ∘ q)) ⁻¹) ∙
          isoComp-cong (preWhisker-isoComp-at (comp-unitʳ f) (lift-base f q h ε) t)
            (idIso ((comp-assoc t h (f ∘ q)) ⁻¹))))

      comparison : restricted-normalization π H h frame t =₂
        ((f ◁ point-frame) ∙ projected-at)
      comparison = isoComp-assoc-at (f ◁ point-frame) (comp-assoc (h ∘ t) q f)
        (transport-pre π H ζ (h ∘ t)) ∙
        (isoComp-cong outer-normal (idIso (transport-pre π H ζ (h ∘ t))) ∙
        (normalization-pre π H (f ∘ q) ζ h t n ∙
          isoComp-cong
            (isoComp-cong (preWhisker t ◁ frame-normal) (idIso ((comp-assoc t (H ∘ h) π) ⁻¹)))
            (idIso ((π ◁ comp-assoc t h H) ⁻¹))))
```
