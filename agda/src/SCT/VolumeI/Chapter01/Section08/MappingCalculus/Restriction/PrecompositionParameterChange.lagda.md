# Restriction and successive parameter changes

We evaluate the pasted separation squares using the square-projection
calculus from Section 1.4. This retains the chosen currying beta witness,
so that the comparison applies to the actual precomposition functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PrecompositionParameterChangeBase as Base
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PrecompositionParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯 using (cancel-evaluation-route; cancel-evaluation-pairs; append-five; append-square; compose-evaluated-pasting)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductMixedSubstitution 𝒯 M using (separate-substitution)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.Substitution.SubstitutionCoherence 𝒯 M using (mapUncurry-restrict-iterated)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; whisker-mixed-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module ParameterChange {X Y A B E : CAT}
  (f : MAP A B) (k : MAP Y (Map B E)) (h : MAP X Y) where
  open Base.ParameterChange 𝒯 M f k h public

  pasted-image = e ◁ paste Sk Sh
  composite-image = e ◁ productMap-separate (k ∘ h) f

  abstract
    mixed-image : (composite-image ∙ input-action) =₂ (output-action ∙ pasted-image)

    mixed-image = post-square e (paste Sk Sh) (productMap-separate (k ∘ h) f)
      (LZ ◁ κA) (κB ▷ LX) (separate-substitution h k f)
  abstract
    normalize-input : (mapPre-uncurry f (k ∘ h) ∙ τ) =₂
      (output-associator ∙ (composite-image ∙ composite-input))

    normalize-input = append-five output-associator composite-image
      (comp-assoc KHA LZ e) (β ▷ KHA) v τ
  abstract
    move-product : (composite-image ∙ (input-action ∙ z)) =₂
      (output-action ∙ (pasted-image ∙ z))

    move-product = append-square composite-image input-action output-action pasted-image z mixed-image
  abstract
    close-output :
      ((w ▷ LX) ∙ (output-associator ∙ (output-action ∙ (pasted-image ∙ z)))) =₂
      (Pasted.evaluation-action ∙ u)

    close-output = compose-evaluated-pasting (w ▷ LX) output-associator output-action
      pasted-image z Pasted.target-evaluation Pasted.evaluation-action Pasted.source-evaluation u
      output-endpoint pasted-evaluation source-endpoint
  abstract
    comparison :
      ((w ▷ LX) ∙ (mapPre-uncurry f (k ∘ h) ∙ τ)) =₂
      (Pasted.evaluation-action ∙ u)
    comparison = close-output ∙
      (isoComp-cong (idIso (w ▷ LX)) (isoComp-cong (idIso output-associator) move-product) ∙
      (isoComp-cong (idIso (w ▷ LX))
        (isoComp-cong (idIso output-associator) (isoComp-cong (idIso composite-image) input-endpoint)) ∙
        isoComp-cong (idIso (w ▷ LX)) normalize-input))
```
