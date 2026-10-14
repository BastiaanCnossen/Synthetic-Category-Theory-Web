# Evaluating a separation square with units

A square commuting with the chosen product unit comparisons also commutes
with their evaluated comparisons. Naturality retains the specified
identification of the evaluator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedUnitSquare
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (triangle-whiskered; right-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at; postWhisker-comp-at; preWhisker-id-at)

import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedRightUnit as RightUnit

module At {X Y Z : CAT} (JX : MAP X X) (JY : MAP Y Y)
  (δX : JX =₁ id X) (δY : JY =₁ id Y) (h : MAP X Y)
  (S : (h ∘ JX) =₁ (JY ∘ h))
  (square : ((comp-unitˡ h ∙ (δY ▷ h)) ∙ S) =₂ (comp-unitʳ h ∙ (h ◁ δX)))
  (e : MAP Y Z) {U : MAP X Z} (β : U =₁ (e ∘ h)) where
  tE = comp-unitʳ e ∙ (e ◁ δY)
  left = comp-unitˡ h ∙ (δY ▷ h)
  right = comp-unitʳ h ∙ (h ◁ δX)
  before = comp-assoc h JY e
  after = comp-assoc JX h e
  tU = comp-unitʳ U ∙ (U ◁ δX)
  module Right = RightUnit.At 𝒯 JX δX h e β

  abstract
    left-prefix : (tE ▷ h) =₂ ((e ◁ left) ∙ before)
    left-prefix = isoComp-cong ((postWhisker-isoComp-at e (comp-unitˡ h) (δY ▷ h)) ⁻¹) (idIso before) ∙
      (isoComp-assoc-at (e ◁ comp-unitˡ h) (e ◁ (δY ▷ h)) before) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ comp-unitˡ h)) (whisker-mixed-at δY h e) ∙
      isoComp-assoc-at (e ◁ comp-unitˡ h) (comp-assoc h (id Y) e) ((e ◁ δY) ▷ h) ∙
      isoComp-cong (triangle-whiskered h e) (idIso ((e ◁ δY) ▷ h)) ∙
      preWhisker-isoComp-at (comp-unitʳ e) (e ◁ δY) h

    left-core : ((tE ▷ h) ∙ before ⁻¹) =₂ (e ◁ left)
    left-core = cancel-right before (e ◁ left) ∙ isoComp-cong left-prefix (idIso (before ⁻¹))

    right-prefix : ((e ◁ right) ∙ after) =₂
      (comp-unitʳ (e ∘ h) ∙ ((e ∘ h) ◁ δX))
    right-prefix = Right.right-prefix

    beta-slide : ((comp-unitʳ (e ∘ h) ∙ ((e ∘ h) ◁ δX)) ∙ (β ▷ JX)) =₂ (β ∙ tU)
    beta-slide = Right.beta-slide

    value : ((tE ▷ h) ∙ (before ⁻¹ ∙ ((e ◁ S) ∙ (after ∙ (β ▷ JX))))) =₂ (β ∙ tU)
    value = beta-slide ∙ isoComp-cong right-prefix (idIso (β ▷ JX)) ∙
      (isoComp-assoc-at (e ◁ right) after (β ▷ JX)) ⁻¹ ∙
      isoComp-cong ((postWhisker e ◁ square) ∙ (postWhisker-isoComp-at e left S) ⁻¹)
        (idIso (after ∙ (β ▷ JX))) ∙
      (isoComp-assoc-at (e ◁ left) (e ◁ S) (after ∙ (β ▷ JX))) ⁻¹ ∙
      isoComp-cong left-core (idIso ((e ◁ S) ∙ (after ∙ (β ▷ JX)))) ∙
      (isoComp-assoc-at (tE ▷ h) (before ⁻¹) ((e ◁ S) ∙ (after ∙ (β ▷ JX)))) ⁻¹
```
