# Restricting a diagonal cone over two points

Reading the two coordinates commutes with restriction of the cone vertex.
The comparison includes its matching identification, with the associators
from restriction retained throughout.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated

module SCT.VolumeI.Chapter01.Section06.Coordinates.PointDiagonalRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.PointDiagonalCoordinates 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc)

simple-normalization-pre : {R T X Y Z : CAT}
  (π : MAP Y Z) (H : MAP X Y) (k : MAP X Z)
  (β : (π ∘ H) =₁ k) (u : MAP T X) (r : MAP R T) →
  (restricted-normalization π H u (transport-pre π H β u) r) =₂
    ((comp-assoc r u k) ⁻¹ ∙ transport-pre π H β (u ∘ r))
simple-normalization-pre π H k β u r =
  (move-square A (old ∙ corner) next edge
    (transport-pre-assoc π H k β u r ∙ (isoComp-assoc-at A old corner) ⁻¹)) ⁻¹
  where
  A = comp-assoc r u k
  old = transport-pre π H β u ▷ r
  corner = (comp-assoc r (H ∘ u) π) ⁻¹
  next = transport-pre π H β (u ∘ r)
  edge = π ◁ comp-assoc r u H

module Restriction {E S T : CAT} (f g : Obj-abs E)
  (t : Cone (pair f g) (pair (id E) (id E)) T) (r : MAP S T) where

  open Coordinates f g
  u = Cone.left t
  v = Cone.right t
  restricted = conePre r t
  A = comp-assoc r u f
  B = comp-assoc r u g
  x = edge₁ t ▷ r
  y = edge₂ t ▷ r

  opaque
    first : (edge₁ restricted) =₂ (x ∙ A ⁻¹)
    first = coordinate-pre pr₁ t r (left₁ u) (right₁ v) (left₁ (u ∘ r)) (right₁ (v ∘ r)) (A ⁻¹)
      (simple-normalization-pre pr₁ F f (pair-β₁ f g) u r)
      (identity-normalization-pre pr₁ Δ (pair-β₁ (id E) (id E)) v r)

    second : (edge₂ restricted) =₂ (y ∙ B ⁻¹)
    second = coordinate-pre pr₂ t r (left₂ u) (right₂ v) (left₂ (u ∘ r)) (right₂ (v ∘ r)) (B ⁻¹)
      (simple-normalization-pre pr₂ F g (pair-β₂ f g) u r)
      (identity-normalization-pre pr₂ Δ (pair-β₂ (id E) (id E)) v r)

    matching-pre : ((edge₂ t) ⁻¹ ∙ edge₁ t) ▷ r =₂ (y ⁻¹ ∙ x)
    matching-pre = isoComp-cong (pre-inverse (edge₂ t) r) (idIso x) ∙
      preWhisker-isoComp-at ((edge₂ t) ⁻¹) (edge₁ t) r

    matching : Cone.match (from restricted) =₂ Cone.match (conePre r (from t))
    matching = isoComp-cong (idIso B) (isoComp-cong (matching-pre ⁻¹) (idIso (A ⁻¹))) ∙
      (isoComp-cong (idIso B) ((isoComp-assoc-at (y ⁻¹) x (A ⁻¹)) ⁻¹) ∙
      (isoComp-assoc-at B (y ⁻¹) (x ∙ A ⁻¹) ∙
      (isoComp-cong (isoComp-cong (inverse-inverse B) (idIso (y ⁻¹)) ∙ inverse-composite y (B ⁻¹)) (idIso (x ∙ A ⁻¹)) ∙
        isoComp-cong (＝-inv ◁ second) first)))

  comparison : ConeIso (from restricted) (conePre r (from t))
  comparison = cone-match-change _ _ _ _ matching
```
