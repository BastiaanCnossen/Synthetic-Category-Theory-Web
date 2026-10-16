# Postcomposition preserves comparisons of framed morphism families

A functor carries a comparison of arrow families together with its two
endpoint equations to the corresponding comparison of image families.
The proof uses change of base for endpoint triangles followed by their
composition with the existing evaluation comparison. Thus it retains the
specified frames of `map-morphism-family`.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.MorphismFamilyPostcomposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc; comp₌-cong)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle; restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (CompatibleOver; compose-triangle; compatible-post; compatible-postcompose)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; evAt; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (evAt-post; map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (family-comparison; module FamilyComparison)

private
  module ImageFrame {Γ : Context} {P U V C D : CAT Γ}
    (F : MAP C D) (before : MAP U C) (after : MAP V D)
    (K : MAP U V) (boundary : (after ∘ K) =₁ (F ∘ before))
    {x : MAP P C} {u v : MAP P U}
    (p : (before ∘ u) =₁ x) (q : (before ∘ v) =₁ x)
    (delta : u =₁ v) (given : CompatibleOver before p q delta) where
    frame : (h : MAP P U) → (before ∘ h) =₁ x → (after ∘ (K ∘ h)) =₁ (F ∘ x)
    frame h r = (F ◁ r) ∙
      (comp-assoc h before F ∙ ((boundary ▷ h) ∙ (comp-assoc h K after) ⁻¹))

    private
      normalize : (h : MAP P U) (r : (before ∘ h) =₁ x)
        → compose-triangle after K boundary h (post-triangle F before h r) =₂ frame h r
      normalize h r = comp₌-assoc (F ◁ r) (comp-assoc h before F)
        (restrict-triangle after K boundary h)
      composed : CompatibleOver after
        (compose-triangle after K boundary u (post-triangle F before u p))
        (compose-triangle after K boundary v (post-triangle F before v q)) (K ◁ delta)
      composed = compatible-post after K boundary
        (post-triangle F before u p) (post-triangle F before v q) delta
        (compatible-postcompose F before p q delta given)

    compatibility : CompatibleOver after (frame u p) (frame v q) (K ◁ delta)
    compatibility = normalize u p ∙
      (composed ∙ comp₌-cong ((normalize v q) ⁻¹) (id₌ (after ◁ (K ◁ delta))))

module _ {Γ : Context} where
  post-family-comparison : {P C D : CAT Γ} (F : MAP C D) {f g : MAP P C}
    {alpha beta : MorphismFamily f g}
    → MorphismFamilyIdentification One alpha beta
    → MorphismFamilyIdentification One (map-morphism-family F alpha) (map-morphism-family F beta)
  post-family-comparison {C = C} {D} F {alpha = alpha} {beta} given =
    family-comparison (map-morphism-family F alpha) (map-morphism-family F beta)
      (funPost F ◁ Comparison.identification)
      (ImageFrame.compatibility F (evAt {C = C} zero) (evAt {C = D} zero)
        (funPost F) (evAt-post zero F)
        (MorphismFamily.source-frame alpha) (MorphismFamily.source-frame beta)
        Comparison.identification Comparison.source)
      (ImageFrame.compatibility F (evAt {C = C} one) (evAt {C = D} one)
        (funPost F) (evAt-post one F)
        (MorphismFamily.target-frame alpha) (MorphismFamily.target-frame beta)
        Comparison.identification Comparison.target)
    where module Comparison = FamilyComparison given
```
