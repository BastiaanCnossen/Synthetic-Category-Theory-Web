# Evaluation along compatible sections

A square relating two chosen sections carries evaluation along one section
to evaluation along the other. The comparison uses its specified projection
triangle and its full compatibility with both section triangles. Applying
this to insertion at a point retains the original parameter comparison.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.InsertionSectionEvaluation where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; post-triangle; post-square-cell)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-restrict-triangle; post-triangle-change)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (triangle-whiskered)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation using (module SectionEvaluation)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters using (module ParameterInsertion)
open import SCT.VolumeI.Chapter02.Section01.InsertionSectionComparison using (module InsertionSectionComparison)

module SectionEvaluationChange {Γ : Context} {P Q K L C : CAT Γ}
  (pi : MAP K P) (rho : MAP L Q) (j : MAP P K) (i : MAP Q L)
  (bP : (pi ∘ j) =₁ id P) (bQ : (rho ∘ i) =₁ id Q)
  (r : MAP Q P) (J : MAP L K) (beta : (pi ∘ J) =₁ (r ∘ rho))
  (nu : (j ∘ r) =₁ (J ∘ i))
  (square : ((SectionEvaluation.image rho i bQ r ∙ restrict-triangle pi J beta i) ∙ (pi ◁ nu)) =₂
    (comp-unitˡ r ∙ restrict-triangle pi j bP r)) (f : MAP P C) where
  module Before = SectionEvaluation pi j bP
  module After = SectionEvaluation rho i bQ
  comparison : ((f ∘ pi) ∘ J) =₁ ((f ∘ r) ∘ rho)
  comparison = post-square-cell f rho r pi J beta
  route : (((f ∘ pi) ∘ j) ∘ r) =₁ (((f ∘ pi) ∘ J) ∘ i)
  route = post-square-cell (f ∘ pi) i J j r nu

  private
    w = After.image r ∙ restrict-triangle pi J beta i
    W = post-triangle f pi (J ∘ i) w
    Kappa = post-triangle f pi J beta
    Kappa-i = Kappa ▷ i
    B = comp-assoc rho r f ▷ i
    A = comp-assoc i J (f ∘ pi)
    S = post-triangle f (r ∘ rho) i (After.image r)
    V = post-triangle (f ∘ pi) j r nu
    old-post = post-triangle f pi j bP
    old-r = old-post ▷ r
    input-middle = comp-assoc r (id P) f
    comparison-image : (comparison ▷ i) =₂ (B ⁻¹ ∙ Kappa-i)
    comparison-image = comp₌-cong (preWhisker-inverse (comp-assoc rho r f) i) (id₌ Kappa-i) ∙
      preWhisker-comp₌ ((comp-assoc rho r f) ⁻¹) Kappa i
    cancel-comparison : (After.image (f ∘ r) ∙ (comparison ▷ i)) =₂ (S ∙ Kappa-i)
    cancel-comparison = comp₌-cong (id₌ S) (comp-inv-left B Kappa-i) ∙
      (comp₌-assoc S B (B ⁻¹ ∙ Kappa-i) ∙
        comp₌-cong (After.postcompose r f) comparison-image)
    joined : (W ∙ A) =₂ (S ∙ Kappa-i)
    joined = ((comp₌-assoc (f ◁ After.image r) (comp-assoc i (r ∘ rho) f) Kappa-i) ⁻¹) ∙
      (post-restrict-triangle f pi J i beta (After.image r) ∙
        comp₌-assoc (f ◁ w) (comp-assoc (J ∘ i) pi f) A)
    output-normal : (After.image (f ∘ r) ∙ ((comparison ▷ i) ∙ A ⁻¹)) =₂ W
    output-normal = comp-inv-right W A ∙
      (comp₌-cong (joined ⁻¹) (id₌ (A ⁻¹)) ∙
        (comp₌-cong cancel-comparison (id₌ (A ⁻¹)) ∙
          (comp₌-assoc (After.image (f ∘ r)) (comparison ▷ i) (A ⁻¹)) ⁻¹))
    projection-change : (W ∙ V) =₂ ((f ◁ comp-unitˡ r) ∙ (input-middle ∙ old-r))
    projection-change = post-triangle-change f pi j r (J ∘ i) nu bP w (comp-unitˡ r) square
    evaluated-change : (W ∙ V) =₂ (Before.image f ▷ r)
    evaluated-change = ((preWhisker-comp₌ (comp-unitʳ f) old-post r) ⁻¹) ∙
      (comp₌-cong ((triangle-whiskered r f) ⁻¹) (id₌ old-r) ∙
        (((comp₌-assoc (f ◁ comp-unitˡ r) input-middle old-r) ⁻¹) ∙ projection-change))

  compatibility :
    (After.image (f ∘ r) ∙ ((comparison ▷ i) ∙ route)) =₂ (Before.image f ▷ r)
  compatibility = evaluated-change ∙
    (comp₌-cong output-normal (id₌ V) ∙
      (((comp₌-assoc (After.image (f ∘ r)) ((comparison ▷ i) ∙ A ⁻¹) V) ⁻¹) ∙
        comp₌-cong (id₌ (After.image (f ∘ r)))
          ((comp₌-assoc (comparison ▷ i) (A ⁻¹) V) ⁻¹)))

module InsertionSectionEvaluation {Γ : Context} {I P Q C : CAT Γ}
  (a : MAP One I) (r : MAP Q P) (f : MAP P C) =
  SectionEvaluationChange pr₁ pr₁ (insert {P = P} a) (insert {P = Q} a)
    (pair-β₁ (id P) (const {P = P} a)) (pair-β₁ (id Q) (const {P = Q} a))
    r (productMap r (id I)) (pair-β₁ (r ∘ pr₁) (id I ∘ pr₂))
    (ParameterInsertion.value a r) (InsertionSectionComparison.compatibility a r) f
```
