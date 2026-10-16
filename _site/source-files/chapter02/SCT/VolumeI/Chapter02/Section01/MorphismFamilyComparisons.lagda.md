# Comparisons of framed morphism families

Identity, inverse and composition retain the two endpoint equations of a
comparison. The calculation is performed over an arbitrary projection before
specialization to the source and target evaluations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; postWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitʳ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (CompatibleOver; compatible-inverse; compatible-comp)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (MorphismFamily; MorphismFamilyIdentification; ev₀; ev₁)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations
  using (family-comparison; module FamilyComparison)

private
  module _ {Γ : Context} {P U C : CAT Γ} (pi : MAP U C)
    {u : MAP P U} {x : MAP P C} (p : (pi ∘ u) =₁ x) where
    identity-compatible : CompatibleOver pi p p (id₌ u)
    identity-compatible = comp₌-unitʳ-One p ∙
      comp₌-cong (id₌ p) (postWhisker-id₌ pi u)

module _ {Γ : Context} where
  id-family-comparison : {P C : CAT Γ} {f g : MAP P C} (alpha : MorphismFamily f g)
    → MorphismFamilyIdentification One alpha alpha
  id-family-comparison alpha = family-comparison alpha alpha (id₌ (MorphismFamily.arrow alpha))
    (identity-compatible ev₀ (MorphismFamily.source-frame alpha))
    (identity-compatible ev₁ (MorphismFamily.target-frame alpha))

  inverse-family-comparison : {P C : CAT Γ} {f g : MAP P C}
    {alpha beta : MorphismFamily f g}
    → MorphismFamilyIdentification One alpha beta → MorphismFamilyIdentification One beta alpha
  inverse-family-comparison {alpha = alpha} {beta} given =
    family-comparison beta alpha (Q.identification ⁻¹)
      (compatible-inverse ev₀ (MorphismFamily.source-frame alpha) (MorphismFamily.source-frame beta)
        Q.identification Q.source)
      (compatible-inverse ev₁ (MorphismFamily.target-frame alpha) (MorphismFamily.target-frame beta)
        Q.identification Q.target)
    where module Q = FamilyComparison given

  compose-family-comparisons : {P C : CAT Γ} {f g : MAP P C}
    {alpha beta gamma : MorphismFamily f g}
    → MorphismFamilyIdentification One beta gamma → MorphismFamilyIdentification One alpha beta
    → MorphismFamilyIdentification One alpha gamma
  compose-family-comparisons {alpha = alpha} {beta} {gamma} second first =
    family-comparison alpha gamma (S.identification ∙ F.identification)
      (compatible-comp ev₀ (MorphismFamily.source-frame alpha) (MorphismFamily.source-frame beta)
        (MorphismFamily.source-frame gamma) S.identification F.identification S.source F.source)
      (compatible-comp ev₁ (MorphismFamily.target-frame alpha) (MorphismFamily.target-frame beta)
        (MorphismFamily.target-frame gamma) S.identification F.identification S.target F.target)
    where
      module F = FamilyComparison first
      module S = FamilyComparison second
```
