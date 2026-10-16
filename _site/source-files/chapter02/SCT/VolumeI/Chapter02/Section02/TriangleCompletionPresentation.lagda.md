# A completed composable pair presents its long edge

A triangle whose two short edges are compared with a prescribed composable
pair has a long-edge family. Frame its endpoints through the two outer
corner matchings and the supplied short-edge comparisons. This gives a
complete presentation without changing the chosen composite. The existing
presentation theorem then compares the chosen composite with that family.

Applying this construction to the chosen Segal completion supplies such a
presentation for every pair. Keeping the long-edge family separate avoids
recomputing the chosen composite's projected endpoint frames.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TriangleCompletionPresentation where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; postWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; inv-comp-left)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitʳ-One)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
  using (cone-compose; cone-inverse; cone-identification-restrict-One; cone-restrict-assoc)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (Triangles; edge₁; triangle-cone; short-edges)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module TriangleCornerFrames)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (TrianglePresentation; triangle-presentation; SourceCorner; TargetCorner; presented-composition)
open import SCT.VolumeI.Chapter02.Section02.SegalComposition using (module ChosenComposition)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

module CompleteTriangle {Γ : Context} {P C : CAT Γ} {f g h : MAP P C}
  (alpha : MorphismFamily f g) (beta : MorphismFamily g h)
  (sigma : MAP P (Triangles C))
  (short : ConeIdentification₁ (cone-restrict sigma (triangle-cone C))
    (MC.ComposableFamilies.cone alpha beta)) where
  private
    module A = MorphismFamily alpha
    module B = MorphismFamily beta
    module Corners = TriangleCornerFrames C
    first = ConeIdentification₁.left short
    second = ConeIdentification₁.right short
    z = edge₁ ∘ sigma
    source-match = Cone.match (cone-restrict sigma Corners.source-cone)
    target-match = Cone.match (cone-restrict sigma Corners.target-cone)
    source-tail = (ev₀ ◁ first) ∙ source-match
    target-tail = (ev₁ ◁ second) ∙ target-match
  long-family : MorphismFamily f h
  long-family = record
    { arrow = z
    ; source-frame = A.source-frame ∙ source-tail
    ; target-frame = B.target-frame ∙ target-tail }
  private
    source : SourceCorner alpha long-family sigma (id₌ z) first
    source = inv-comp-left A.source-frame source-tail ∙
      (comp₌-unitʳ-One ((A.source-frame ⁻¹) ∙ (A.source-frame ∙ source-tail)) ∙
        comp₌-cong (id₌ ((A.source-frame ⁻¹) ∙ (A.source-frame ∙ source-tail)))
          (postWhisker-id₌ ev₀ z))
    target : TargetCorner beta long-family sigma (id₌ z) second
    target = inv-comp-left B.target-frame target-tail ∙
      (comp₌-unitʳ-One ((B.target-frame ⁻¹) ∙ (B.target-frame ∙ target-tail)) ∙
        comp₌-cong (id₌ ((B.target-frame ⁻¹) ∙ (B.target-frame ∙ target-tail)))
          (postWhisker-id₌ ev₁ z))
  presentation : TrianglePresentation alpha beta long-family
  presentation = triangle-presentation sigma first second (id₌ z)
    (ConeIdentification₁.compatible short) source target

module CompletePair {Γ : Context} {P C : CAT Γ} {f g h : MAP P C}
  (segal : IsEquiv (short-edges C)) (alpha : MorphismFamily f g) (beta : MorphismFamily g h) where
  private
    module Chosen = ChosenComposition C segal
    module Input = MC.ComposableFamilies alpha beta
    sigma = Chosen.completion ∘ Input.pair-map
    short : ConeIdentification₁ (cone-restrict sigma (triangle-cone C)) Input.cone
    short = cone-compose Input.pair-image
      (cone-compose (cone-identification-restrict-One Input.pair-map Chosen.completion-image)
        (cone-inverse (cone-restrict-assoc Input.pair-map Chosen.completion (triangle-cone C))))
    module Completed = CompleteTriangle alpha beta sigma short
  open Completed public using (long-family; presentation)
  composite : MorphismFamilyIdentification One (MC.Composition.compose C segal beta alpha) long-family
  composite = presented-composition segal alpha beta long-family presentation
```
