# Evaluation of a represented diagram under postcomposition

A diagram may be presented by a functor together with its actual uncurrying
identification. Applying a functor transports that presentation. Point
evaluation of the transported presentation agrees with native
postcomposition evaluation, retaining the given representation witness.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.RepresentedDiagramPostcomposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (whisker-mixed-One)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-uncurry)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationPostcomposition using (module PointPostcomposition)
open import SCT.VolumeI.Chapter02.Section01.PostcompositionPointNaturality using (module PostcompositionPointsAt)

open import SCT.VolumeI.Chapter01.Section07.DiagramRepresentations using (represented-postcomposition)

module RepresentedDiagramPostcomposition {Γ : Context} {I P C D : CAT Γ}
  (F : MAP C D) (h : MAP P (Fun I C)) (H : MAP (P × I) C)
  (beta : funUncurry h =₁ H) (a : MAP One I) where
  private
    i : MAP P (P × I)
    i = insert a
    U : MAP (P × I) C
    U = funUncurry h
    phi = funPost-uncurry F h
    Q = AtPoint.uncurry-image a (funPost {C = I} F ∘ h)
    before = comp-assoc i U F
    b = (F ◁ beta) ▷ i
    f = phi ▷ i
    image = F ◁ (beta ▷ i)
    module Native = PointPostcomposition.Framed a F h (beta ▷ i)

  representation : funUncurry (funPost {C = I} F ∘ h) =₁ (F ∘ H)
  representation = represented-postcomposition {I = I} {P = P} {C = C} {D = D} F h H beta
  original-point : (evAt a ∘ h) =₁ (H ∘ i)
  original-point = AtPoint.represented-point {I = I} {C = C} a h H beta
  input-assoc : ((F ∘ H) ∘ i) =₁ (F ∘ (H ∘ i))
  input-assoc = comp-assoc i H F
  point-tail : (evAt a ∘ (funPost {C = I} F ∘ h)) =₁ ((F ∘ H) ∘ i)
  point-tail = (representation ▷ i) ∙ Q
  point : (evAt a ∘ (funPost {C = I} F ∘ h)) =₁ (F ∘ (H ∘ i))
  point = input-assoc ∙ point-tail
  native : (evAt a ∘ (funPost {C = I} F ∘ h)) =₁ (F ∘ (H ∘ i))
  native = (F ◁ original-point) ∙ PostcompositionPointsAt.point F h a

  compatibility : (input-assoc ∙ point-tail) =₂ native
  compatibility = Native.frame-image ∙
    (comp₌-cong (whisker-mixed-One beta i F) (id₌ (f ∙ Q)) ∙
      ((comp₌-assoc input-assoc b (f ∙ Q)) ⁻¹ ∙
        (comp₌-cong (id₌ input-assoc) (comp₌-assoc b f Q) ∙
          comp₌-cong (id₌ input-assoc)
            (comp₌-cong (preWhisker-comp₌ (F ◁ beta) phi i) (id₌ Q)))))
```
