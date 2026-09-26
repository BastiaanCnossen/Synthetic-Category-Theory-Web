# Projecting a pasted cone

Projecting the left leg commutes with pasting a cone, after changing the
left cospan by its associator. Both leg comparisons are identities; the
matching comparison is the associator pentagon.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IP

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositePasting
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones; compositeCone)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open IP vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (pentagon-whiskered)

module Pasting {A B C D S Q X : CAT} (π : MAP A B) (k : MAP B C) (b : MAP C D)
  {p : MAP S D} (square : Cone b p Q) (s : Cone (k ∘ π) (Cone.left square) X) where
  l = Cone.left s
  r = Cone.right s
  ν = Cone.match (conePre r square)
  σ = Cone.match s
  α = comp-assoc π k b
  U = comp-assoc l (k ∘ π) b
  V = comp-assoc l π (b ∘ k)
  W = α ▷ l
  K = comp-assoc l π k
  J = comp-assoc (π ∘ l) k b
  η = (α ⁻¹ ▷ l) ⁻¹
  projected = compositeCone π (b ∘ k) (changeLeft (α ⁻¹) (PasteCones.flatten (k ∘ π) b square s))
  pasted = PasteCones.flatten k b square (compositeCone π k s)

  abstract
    inverse-image : η =₂ W
    inverse-image = inverse-inverse W ∙ (＝-inv ◁ pre-inverse α l)

    pentagon : ((U ∙ W) ∙ V ⁻¹) =₂ ((b ◁ (K ⁻¹)) ∙ J)
    pentagon = isoComp-cong ((post-inverse b K) ⁻¹) (idIso J) ∙
      (move-square (b ◁ K) (U ∙ W) J V ((pentagon-whiskered l π k b) ⁻¹)) ⁻¹

    matching : Cone.match projected =₂ Cone.match pasted
    matching = isoComp-cong (idIso ν)
        (isoComp-cong ((postWhisker-isoComp-at b σ (K ⁻¹)) ⁻¹) (idIso J) ∙
          ((isoComp-assoc-at (b ◁ σ) (b ◁ K ⁻¹) J) ⁻¹ ∙
            isoComp-cong (idIso (b ◁ σ)) pentagon)) ∙
      (isoComp-cong (idIso ν) (isoComp-assoc-at (b ◁ σ) (U ∙ W) (V ⁻¹)) ∙
        (isoComp-assoc-at ν ((b ◁ σ) ∙ (U ∙ W)) (V ⁻¹) ∙
          (isoComp-cong
            (isoComp-cong (idIso ν) (isoComp-assoc-at (b ◁ σ) U W) ∙
              (isoComp-assoc-at ν ((b ◁ σ) ∙ U) W ∙
                isoComp-cong (idIso (ν ∙ ((b ◁ σ) ∙ U))) inverse-image))
            (idIso (V ⁻¹)))))

  comparison : ConeIso projected pasted
  comparison = cone-match-change _ _ _ _ matching
```
