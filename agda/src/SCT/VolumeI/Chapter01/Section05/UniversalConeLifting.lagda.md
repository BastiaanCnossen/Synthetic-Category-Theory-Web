# Prescribed comparisons for any pullback cone

The lifting theorem transfers from the chosen pullback to any pullback
cone. The two projection identifications are retained explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section05.UniversalConeLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P
open PN vocabulary terminal products productLaws composition vertical whiskering using (substitution-square-projection)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module UniversalLift {C D E T S : CAT} {f : MAP C E} {g : MAP D E}
  (t : Cone f g T) (et : IsPullback t) (h k : MAP S T)
  (Φ : ConeIso (conePre h t) (conePre k t)) where

  l = pbLift t
  β = pbLift-β t
  compare : (r : MAP S T) → ConeIso (conePre (l ∘ r) (pbCone f g)) (conePre r t)
  compare r = coneIso-compose (coneIso-pre r β) (coneIso-inverse (conePre-assoc r l (pbCone f g)))
  comparison = coneIso-compose (coneIso-inverse (compare k)) (coneIso-compose Φ (compare h))
  module Chosen = Lift (l ∘ h) (l ∘ k) comparison
  lifted = postWhisker-lift l et Chosen.lift
  abstract
    lift : =₁ h k
    lift = FunctorLift.lift lifted

    image : =₂ (l ◁ lift) Chosen.lift
    image = FunctorLift.comparison lifted

  projection-image : {B : CAT} (π : MAP (Pullback f g) B) (q : MAP T B)
    (b : =₁ (π ∘ l) q) (α : =₁ (q ∘ h) (q ∘ k)) →
    =₂ (π ◁ Chosen.lift)
      (invIso ((b ▷ k) ∙ invIso (comp-assoc k l π)) ∙
        (α ∙ ((b ▷ h) ∙ invIso (comp-assoc h l π)))) → =₂ (q ◁ lift) α
  projection-image π q b α prescribed = cancel-right-reflect bh
    (cancel-inverse bk (α ∙ bh) ∙
    (isoComp-cong (idIso bk) prescribed ∙
    (isoComp-cong (idIso bk) (postWhisker π ◁ image) ∙
      invIso (substitution-square-projection π l q b lift))))
    where
    bh = (b ▷ h) ∙ invIso (comp-assoc h l π)
    bk = (b ▷ k) ∙ invIso (comp-assoc k l π)

  left-image : =₂ (Cone.left t ◁ lift) (ConeIso.leftIso Φ)
  left-image = projection-image pb₁ (Cone.left t) (ConeIso.leftIso β) (ConeIso.leftIso Φ) Chosen.left-image

  right-image : =₂ (Cone.right t ◁ lift) (ConeIso.rightIso Φ)
  right-image = projection-image pb₂ (Cone.right t) (ConeIso.rightIso β) (ConeIso.rightIso Φ) Chosen.right-image
```
