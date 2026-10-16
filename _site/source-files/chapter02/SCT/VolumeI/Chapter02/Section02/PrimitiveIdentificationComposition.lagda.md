# Composition of primitive identifications as morphisms

Retarget the full source-unit presentation at `x` by the three vertex
identifications `id`, `p`, and `q ∙ p`. Its first and long edges retain
the constant arrow at `x`. Changing the object of the second constant
arrow identifies it with the original conversion of `q` at `y`.
All three corner comparisons are transported together. The Segal
comparison with this presentation proves compatibility of the actual
conversion with composition, retaining both prescribed endpoint frames.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.PrimitiveIdentificationComposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; postWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc; comp₌-cong)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One; comp₌-unitʳ-One)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification; identity-family; identification-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations
  using (retarget-family; family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.IdentityFamilyTransport using (module IdentityFamilyChange)
open import SCT.VolumeI.Chapter02.Section02.SegalAxiom using (segal-isEquiv)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionUnits using (module FamilyUnitPresentations)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (TrianglePresentation; presented-composition; module RetargetPresentation)
open import SCT.VolumeI.Chapter02.Section02.TrianglePresentationChange using (module ReplacePresentation)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

private
  module ConvertedTriangle {Γ : Context} {P C : CAT Γ} {x y z : MAP P C}
    (p : x =₁ y) (q : y =₁ z) where
    private
      module X = MorphismFamily (identity-family x)
      module Y = MorphismFamily (identity-family y)
      module Changed = FamilyComparison (IdentityFamilyChange.value p)
        using (identification; source; target)

    normalized : {v : MAP P C} (r : x =₁ v)
      → MorphismFamilyIdentification One
          (retarget-family (identity-family x) (id₌ x) r) (identification-family r)
    normalized r = family-comparison _ _ (id₌ X.arrow)
      ((comp₌-unitˡ-One X.source-frame) ⁻¹ ∙
        (comp₌-unitʳ-One X.source-frame ∙
          comp₌-cong (id₌ X.source-frame) (postWhisker-id₌ ev₀ X.arrow)))
      (comp₌-unitʳ-One (r ∙ X.target-frame) ∙
        comp₌-cong (id₌ (r ∙ X.target-frame)) (postWhisker-id₌ ev₁ X.arrow))

    second : MorphismFamilyIdentification One
      (retarget-family (identity-family x) p (q ∙ p)) (identification-family q)
    second = family-comparison _ _ Changed.identification Changed.source
      ((comp₌-assoc q p X.target-frame) ⁻¹ ∙
        (comp₌-cong (id₌ q) Changed.target ∙
          comp₌-assoc q Y.target-frame (ev₁ ◁ Changed.identification)))

    presentation : TrianglePresentation
      (identification-family p) (identification-family q) (identification-family (q ∙ p))
    presentation = ReplacePresentation.value
      (RetargetPresentation.value (FamilyUnitPresentations.source (identity-family x))
        (id₌ x) p (q ∙ p))
      (normalized p) second (normalized (q ∙ p))

module _ {Γ : Context} {P C : CAT Γ} {x y z : MAP P C} where
  identification-composition : (p : x =₁ y) (q : y =₁ z)
    → MorphismFamilyIdentification One
        (MC.Composition.compose C (segal-isEquiv C)
          (identification-family q) (identification-family p))
        (identification-family (q ∙ p))
  identification-composition p q = presented-composition (segal-isEquiv C)
    (identification-family p) (identification-family q) (identification-family (q ∙ p))
    (ConvertedTriangle.presentation p q)
```
