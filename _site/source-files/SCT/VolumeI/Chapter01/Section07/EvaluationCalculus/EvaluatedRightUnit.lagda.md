# Evaluation and a specified right unit

Right-unit coherence and naturality carry a specified identification of
an evaluator through a comparison to the identity functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedRightUnit
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (right-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; preWhisker-id-at)

module At {X Y Z : CAT} (JX : MAP X X) (δX : JX =₁ id X)
  (h : MAP X Y) (e : MAP Y Z) {U : MAP X Z} (β : U =₁ (e ∘ h)) where
  right = comp-unitʳ h ∙ (h ◁ δX)
  after = comp-assoc JX h e
  tU = comp-unitʳ U ∙ (U ◁ δX)

  abstract
    right-prefix : ((e ◁ right) ∙ after) =₂
      (comp-unitʳ (e ∘ h) ∙ ((e ∘ h) ◁ δX))
    right-prefix = isoComp-cong ((right-unitor-comp h e) ⁻¹) (idIso ((e ∘ h) ◁ δX)) ∙
      (isoComp-assoc-at (e ◁ comp-unitʳ h) (comp-assoc (id X) h e) ((e ∘ h) ◁ δX)) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ comp-unitʳ h)) ((postWhisker-comp-at δX h e) ⁻¹) ∙
      isoComp-assoc-at (e ◁ comp-unitʳ h) (e ◁ (h ◁ δX)) after ∙
      isoComp-cong (postWhisker-isoComp-at e (comp-unitʳ h) (h ◁ δX)) (idIso after)

    beta-slide : ((comp-unitʳ (e ∘ h) ∙ ((e ∘ h) ◁ δX)) ∙ (β ▷ JX)) =₂ (β ∙ tU)
    beta-slide = isoComp-assoc-at β (comp-unitʳ U) (U ◁ δX) ∙
      isoComp-cong (preWhisker-id-at β) (idIso (U ◁ δX)) ∙
      (isoComp-assoc-at (comp-unitʳ (e ∘ h)) (β ▷ id X) (U ◁ δX)) ⁻¹ ∙
      isoComp-cong (idIso (comp-unitʳ (e ∘ h))) ((interchange-at β δX) ⁻¹) ∙
      isoComp-assoc-at (comp-unitʳ (e ∘ h)) ((e ∘ h) ◁ δX) (β ▷ JX)

    changed-output : {h′ : MAP X Y} (δ : h =₁ h′) (χ : (h ∘ JX) =₁ h′) →
      χ =₂ (δ ∙ right) →
      ((e ◁ χ) ∙ (after ∙ (β ▷ JX))) =₂ (((e ◁ δ) ∙ β) ∙ tU)
    changed-output δ χ square = (isoComp-assoc-at (e ◁ δ) β tU) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ δ)) beta-slide ∙
      isoComp-cong (idIso (e ◁ δ)) (isoComp-cong right-prefix (idIso (β ▷ JX))) ∙
      isoComp-cong (idIso (e ◁ δ)) ((isoComp-assoc-at (e ◁ right) after (β ▷ JX)) ⁻¹) ∙
      isoComp-assoc-at (e ◁ δ) (e ◁ right) (after ∙ (β ▷ JX)) ∙
      isoComp-cong (postWhisker-isoComp-at e δ right ∙ (postWhisker e ◁ square))
        (idIso (after ∙ (β ▷ JX)))
```
