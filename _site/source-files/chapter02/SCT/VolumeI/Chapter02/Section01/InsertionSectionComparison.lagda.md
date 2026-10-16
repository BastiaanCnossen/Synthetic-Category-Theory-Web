# The insertion comparison over its parameter

The chosen insertion comparison is the quotient of two paired evaluations.
Its first projection is therefore the comparison of the corresponding
section evaluations. This calculation retains the actual product projection
triangles, both unitors and the original insertion comparison.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.InsertionSectionComparison where
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
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (postWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; post-triangle; lies-over-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation using (module SectionEvaluation)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-triangle₁-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction using (pair-evaluation-over₁-One)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters using (module ParameterInsertion)

module InsertionSectionComparison {Γ : Context} {I P Q : CAT Γ}
  (a : MAP One I) (r : MAP Q P) where
  module N = ParameterInsertion a
  private
    pi : MAP (P × I) P
    pi = pr₁
    i : MAP Q (Q × I)
    i = insert a
    j : MAP P (P × I)
    j = insert a
    J : MAP (Q × I) (P × I)
    J = productMap r (id I)
    bP = pair-β₁ (id P) (const {P = P} a)
    bQ = pair-β₁ (id Q) (const {P = Q} a)
    betaJ = pair-β₁ (r ∘ pr₁) (id I ∘ pr₂)
    module E = SectionEvaluation pr₁ i bQ
    before = restrict-triangle pi j bP r
    after = E.image r ∙ restrict-triangle pi J betaJ i
    common = pair-β₁ r (const {P = Q} a)
    front = pi ◁ N.front r
    back = pi ◁ N.back r
    first = post-triangle r pr₁ i bQ
    second = post-triangle (id I) pr₂ i (pair-β₂ (id Q) (const {P = Q} a))

    front-image : (common ∙ front) =₂ (comp-unitˡ r ∙ before)
    front-image = pair-evaluation-over₁-One (id P) (const {P = P} a) r
      (comp-unitˡ r) (const-pre a r)
    back-image : (common ∙ back) =₂ after
    back-image = lies-over-comp pi
      (pair-evaluation-over₁-One (r ∘ pr₁) (id I ∘ pr₂) i first second)
      (pair⁼-triangle₁-One (comp-unitʳ r) (comp-unitˡ (const {P = Q} a)))
    quotient-image : (pi ◁ N.value r) =₂ (back ⁻¹ ∙ front)
    quotient-image = comp₌-cong (postWhisker-inverse pi (N.back r)) (id₌ front) ∙
      postWhisker-comp₌ pi (N.back r ⁻¹) (N.front r)

  compatibility :
    ((E.image r ∙ restrict-triangle pi J betaJ i) ∙ (pi ◁ N.value r)) =₂
      (comp-unitˡ r ∙ restrict-triangle pi j bP r)
  compatibility = front-image ∙
    (comp₌-cong (id₌ common) (comp-inv-left back front) ∙
      (comp₌-assoc common back (back ⁻¹ ∙ front) ∙
        comp₌-cong (back-image ⁻¹) quotient-image))
```
