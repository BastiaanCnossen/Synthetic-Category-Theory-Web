# Restricting the two coordinates of a diagonal cone

The comparison below includes the compatibility of the recovered matching.
The two coordinate calculations use the same restricted projection
normalizations, then cancellation identifies their quotient.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup

module SCT.VolumeI.Chapter01.Section05.DiagonalRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.DiagonalCoordinates 𝒯 using (module Coordinates)
open import SCT.VolumeI.Chapter01.Section05.ProjectionRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯
  using (quotient-square; normalize-cone-square)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)

module Restriction {C D E : CAT} (f : MAP C E) (g : MAP D E)
  {S T : CAT} (t : Cone (productMap f g) (pair (id E) (id E)) T) (r : MAP S T) where

  open Coordinates f g
  u = Cone.left t
  v = Cone.right t
  restricted = conePre r t
  l = invIso (comp-assoc r u pr₁)
  q = invIso (comp-assoc r u pr₂)
  A = comp-assoc r (pr₁ ∘ u) f
  B = comp-assoc r (pr₂ ∘ u) g
  firstBoundary = invIso A ∙ (f ◁ l)
  secondBoundary = invIso B ∙ (g ◁ q)

  opaque
    first : =₂ (edge₁ restricted) ((edge₁ t ▷ r) ∙ firstBoundary)
    first = coordinate-pre pr₁ t r (left₁ u) (right₁ v) (left₁ (u ∘ r)) (right₁ (v ∘ r)) firstBoundary
      (composite-normalization-pre pr₁ F pr₁ f (pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) u r)
      (identity-normalization-pre pr₁ Δ (pair-β₁ (id E) (id E)) v r)

    second : =₂ (edge₂ restricted) ((edge₂ t ▷ r) ∙ secondBoundary)
    second = coordinate-pre pr₂ t r (left₂ u) (right₂ v) (left₂ (u ∘ r)) (right₂ (v ∘ r)) secondBoundary
      (composite-normalization-pre pr₂ F pr₂ g (pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) u r)
      (identity-normalization-pre pr₂ Δ (pair-β₂ (id E) (id E)) v r)

    matching-pre : =₂ ((invIso (edge₂ t) ∙ edge₁ t) ▷ r)
      (invIso (edge₂ t ▷ r) ∙ (edge₁ t ▷ r))
    matching-pre = isoComp-cong (pre-inverse (edge₂ t) r) (idIso (edge₁ t ▷ r)) ∙
      preWhisker-isoComp-at (invIso (edge₂ t)) (edge₁ t) r

  comparison : ConeIso (from restricted) (conePre r (from t))
  comparison = record
    { leftIso = l ; rightIso = q
    ; compatible = normalize-cone-square A B (invIso (edge₂ t ▷ r) ∙ (edge₁ t ▷ r))
        (Cone.match (from restricted)) (f ◁ l) (g ◁ q)
        (quotient-square (edge₁ restricted) (edge₂ restricted) (edge₁ t ▷ r) (edge₂ t ▷ r)
          firstBoundary secondBoundary (idIso (v ∘ r))
          (invIso (isoComp-unitˡ-at (edge₁ restricted)) ∙ invIso first)
          (invIso (isoComp-unitˡ-at (edge₂ restricted)) ∙ invIso second)) ∙
        isoComp-cong (isoComp-cong (idIso B) (isoComp-cong matching-pre (idIso (invIso A)))) (idIso (f ◁ l)) }
```
