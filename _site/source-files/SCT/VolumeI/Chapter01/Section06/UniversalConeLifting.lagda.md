# Prescribed comparisons for any pullback cone

The lifting theorem transfers from the chosen pullback to any pullback
cone. The two projection identifications are retained explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section06.UniversalConeLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackLifting 𝒯 P
open PN vocabulary terminal products productLaws composition vertical whiskering using (substitution-square-projection)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module UniversalLift {C D E T S : CAT} {f : MAP C E} {g : MAP D E}
  (t : Cone f g T) (et : IsPullback t) (h k : MAP S T)
  (Φ : ConeIso (conePre h t) (conePre k t)) where

  l = pullbackLift t
  β = pullbackLift-β t
  compare : (r : MAP S T) → ConeIso (conePre (l ∘ r) (pullbackCone f g)) (conePre r t)
  compare r = coneIso-compose (coneIso-pre r β) (coneIso-inverse (conePre-assoc r l (pullbackCone f g)))
  comparison = coneIso-compose (coneIso-inverse (compare k)) (coneIso-compose Φ (compare h))
  module Chosen = Lift (l ∘ h) (l ∘ k) comparison
  lifted = postWhisker-lift l et Chosen.lift
  abstract
    lift : h =₁ k
    lift = FunctorLift.lift lifted

    image : (l ◁ lift) =₂ Chosen.lift
    image = FunctorLift.comparison lifted

  projection-image : {B : CAT} (π : MAP (Pullback f g) B) (q : MAP T B)
    (b : (π ∘ l) =₁ q) (α : (q ∘ h) =₁ (q ∘ k)) →
    (π ◁ Chosen.lift) =₂
      (((b ▷ k) ∙ (comp-assoc k l π) ⁻¹) ⁻¹ ∙
        (α ∙ ((b ▷ h) ∙ (comp-assoc h l π) ⁻¹))) → (q ◁ lift) =₂ α
  projection-image π q b α prescribed = cancel-right-reflect bh
    (cancel-inverse bk (α ∙ bh) ∙
    (isoComp-cong (idIso bk) prescribed ∙
    (isoComp-cong (idIso bk) (postWhisker π ◁ image) ∙
      (substitution-square-projection π l q b lift) ⁻¹)))
    where
    bh = (b ▷ h) ∙ (comp-assoc h l π) ⁻¹
    bk = (b ▷ k) ∙ (comp-assoc k l π) ⁻¹

  left-image : (Cone.left t ◁ lift) =₂ (ConeIso.leftIso Φ)
  left-image = projection-image pullback₁ (Cone.left t) (ConeIso.leftIso β) (ConeIso.leftIso Φ) Chosen.left-image

  right-image : (Cone.right t ◁ lift) =₂ (ConeIso.rightIso Φ)
  right-image = projection-image pullback₂ (Cone.right t) (ConeIso.rightIso β) (ConeIso.rightIso Φ) Chosen.right-image
```
