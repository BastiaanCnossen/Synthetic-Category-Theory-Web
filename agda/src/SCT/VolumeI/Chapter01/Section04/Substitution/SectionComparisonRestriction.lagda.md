# Restricting a comparison evaluated along a section

A comparison into a functor pulled back along a split projection can be
evaluated along the section and then restricted, or restricted and then
evaluated. The comparison and the section witness remain specified.
This is the retraction calculation needed when comparing the two chosen
short-edge formulas for Segal composition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality

module SCT.VolumeI.Chapter01.Section04.Substitution.SectionComparisonRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (compose-base; lift-base)
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-comp-at)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module At {X K Y R : CAT} (π : MAP K X) (i : MAP X K)
  (b : (π ∘ i) =₁ (id X)) (h : MAP X Y) (k : MAP K Y)
  (η : k =₁ (h ∘ π)) (r : MAP R X) where

  along-section = section-image π i b h
  restricted-section = compose-base π i b r (comp-unitˡ r)
  A = comp-assoc r i (h ∘ π)
  B = comp-assoc r i k

  abstract
    section-restricted :
      (lift-base h π (i ∘ r) restricted-section) =₂
      ((along-section ▷ r) ∙ A ⁻¹)
    section-restricted = isoComp-unitˡ-at _ ∙ (section-pre π i b r h) ⁻¹

    comparison :
      (lift-base h π (i ∘ r) restricted-section ∙ (η ▷ (i ∘ r))) =₂
      (((along-section ∙ (η ▷ i)) ▷ r) ∙ B ⁻¹)
    comparison =
      isoComp-cong ((preWhisker-isoComp-at along-section (η ▷ i) r) ⁻¹) (idIso (B ⁻¹)) ∙
      ((isoComp-assoc-at (along-section ▷ r) ((η ▷ i) ▷ r) (B ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso (along-section ▷ r))
        (move-square A ((η ▷ i) ▷ r) (η ▷ (i ∘ r)) B (preWhisker-comp-at η i r)) ∙
      (isoComp-assoc-at (along-section ▷ r) (A ⁻¹) (η ▷ (i ∘ r)) ∙
        isoComp-cong section-restricted (idIso (η ▷ (i ∘ r))))))
```
