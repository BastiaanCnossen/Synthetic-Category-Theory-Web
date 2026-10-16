# Functors preserve the chosen composition of framed families

Choose a completion of the two source arrows. Its long edge, framed through
the outer corners, is compared with the actual chosen source composite.
Postcomposition carries this whole triangle presentation into the target,
where its long edge is also compared with the actual chosen target composite.
The quotient of those two comparisons proves preservation, including both
specified endpoint frames. No equality of inverse choices is required.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.MorphismCompositionPostcomposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (compatible-quotient)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyPostcomposition using (post-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
open import SCT.VolumeI.Chapter02.Section02.TriangleCompletionPresentation using (module CompletePair)
open import SCT.VolumeI.Chapter02.Section02.TrianglePresentationPostcomposition using (module PostPresentation)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

module FunctorComposition {Γ : Context} {C D : CAT Γ} (F : MAP C D)
  (source-segal : IsEquiv (short-edges C)) (target-segal : IsEquiv (short-edges D)) where
  preserves-composition : {P : CAT Γ} {f g h : MAP P C}
    (beta : MorphismFamily g h) (alpha : MorphismFamily f g)
    → MorphismFamilyIdentification One
        (map-morphism-family F (MC.Composition.compose C source-segal beta alpha))
        (MC.Composition.compose D target-segal (map-morphism-family F beta) (map-morphism-family F alpha))
  preserves-composition beta alpha = family-comparison _ _
    ((Target.identification ⁻¹) ∙ Source.identification)
    (compatible-quotient ev₀ _ _ _ Source.identification Target.identification Source.source Target.source)
    (compatible-quotient ev₁ _ _ _ Source.identification Target.identification Source.target Target.target)
    where
      module Completed = CompletePair source-segal alpha beta
      module Source = FamilyComparison (post-family-comparison F Completed.composite)
      module Target = FamilyComparison (PostPresentation.composite F Completed.presentation target-segal)
```
