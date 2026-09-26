# Evaluating a comparison along a section

A comparison into a functor pulled back along a split projection can be
evaluated before or after postcomposition. The calculation retains the
comparison itself, the section witness, and both associators.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section04.Substitution.SectionComparisonEvaluation
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

module At {X K Y Z : CAT} (π : MAP K X) (i : MAP X K)
  (b : (π ∘ i) =₁ (id X)) (h : MAP X Y) (k : MAP K Y)
  (η : k =₁ (h ∘ π)) (z : MAP Y Z) where
  δ = (comp-assoc π h z) ⁻¹ ∙ (z ◁ η)
  S = section-image π i b h
  A = comp-assoc π h z ▷ i
  B = (z ◁ η) ▷ i
  C = comp-assoc i (h ∘ π) z
  E = comp-assoc i k z
  F = z ◁ S

  abstract
    restricted : (δ ▷ i) =₂ (A ⁻¹ ∙ B)
    restricted = isoComp-cong (pre-inverse (comp-assoc π h z) i) (idIso B) ∙
      preWhisker-isoComp-at ((comp-assoc π h z) ⁻¹) (z ◁ η) i

    cancel : (((F ∙ C) ∙ A) ∙ (A ⁻¹ ∙ B)) =₂ ((F ∙ C) ∙ B)
    cancel = isoComp-cong (idIso (F ∙ C)) (cancel-inverse A B) ∙
      isoComp-assoc-at (F ∙ C) A (A ⁻¹ ∙ B)

    comparison : (section-image π i b (z ∘ h) ∙ (δ ▷ i)) =₂
      ((z ◁ (section-image π i b h ∙ (η ▷ i))) ∙ comp-assoc i k z)
    comparison = isoComp-cong ((postWhisker-isoComp-at z S (η ▷ i)) ⁻¹) (idIso E) ∙
      ((isoComp-assoc-at F (z ◁ (η ▷ i)) E) ⁻¹ ∙
      (isoComp-cong (idIso F) (whisker-mixed-at η i z) ∙
      (isoComp-assoc-at F C B ∙
      (cancel ∙ isoComp-cong (section-comp π i b h z) restricted))))
```
