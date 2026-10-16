# The chosen composite and comparison of its inputs

Every composable pair has a complete triangle presentation whose long edge
is the actual chosen composite. Start with its Segal completion, whose long
edge is framed directly by the outer corners. Its comparison with chosen
composition replaces that long edge, retaining all three corner squares.

Changing the two framed inputs then gives comparison of their chosen
composites. This uses the same presentation interface as unit laws and
functor preservation; no new edgewise calculation or inverse choice is needed.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.MorphismCompositionComparisons where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons
  using (id-family-comparison; inverse-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (TrianglePresentation; presented-composition)
open import SCT.VolumeI.Chapter02.Section02.TrianglePresentationChange using (module ReplacePresentation)
open import SCT.VolumeI.Chapter02.Section02.TriangleCompletionPresentation using (module CompletePair)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

module CompositionComparisons {Γ : Context} (C : CAT Γ) (segal : IsEquiv (short-edges C)) where
  private
    module Chosen = MC.Composition C segal

  composition-presentation : {P : CAT Γ} {f g h : MAP P C}
    (beta : MorphismFamily g h) (alpha : MorphismFamily f g)
    → TrianglePresentation alpha beta (Chosen.compose beta alpha)
  composition-presentation beta alpha = ReplacePresentation.value Completed.presentation
    (id-family-comparison alpha) (id-family-comparison beta)
    (inverse-family-comparison Completed.composite)
    where module Completed = CompletePair segal alpha beta

  composition-comparison : {P : CAT Γ} {f g h : MAP P C}
    {alpha alpha′ : MorphismFamily f g} {beta beta′ : MorphismFamily g h}
    → MorphismFamilyIdentification One beta beta′ → MorphismFamilyIdentification One alpha alpha′
    → MorphismFamilyIdentification One (Chosen.compose beta alpha) (Chosen.compose beta′ alpha′)
  composition-comparison {alpha = alpha} {alpha′} {beta} {beta′} second first =
    inverse-family-comparison
      (presented-composition segal alpha′ beta′ (Chosen.compose beta alpha)
        (ReplacePresentation.value (composition-presentation beta alpha) first second
          (id-family-comparison (Chosen.compose beta alpha))))
```
