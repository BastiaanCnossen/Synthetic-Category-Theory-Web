# Evaluating a represented diagram after parameter change

A chosen identification from an uncurried family to a diagram can be
restricted along a parameter map. Evaluating this restricted representation
at a point agrees with restricting its original point evaluation and
transporting along the specified insertion square. The original uncurry
comparison and evaluation restriction are retained.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.RestrictedDiagramEvaluation where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-square-cell; post-square-cell-outer)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-restrict)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters
  using (module ParameterInsertion; module UncurryParameter)

open import SCT.VolumeI.Chapter01.Section07.DiagramRepresentations using (represented-restriction)

module _ {Γ : Context} where
  parameter-square-image : {I C P Q : CAT Γ}
    (a : MAP One I) (D : MAP (P × I) C) (r : MAP Q P)
    → ((D ∘ insert {P = P} a) ∘ r) =₁
      ((D ∘ productMap r (id I)) ∘ insert {P = Q} a)
  parameter-square-image {I = I} {P = P} {Q = Q} a D r =
    post-square-cell D (insert {P = Q} a) (productMap r (id I))
      (insert {P = P} a) r (ParameterInsertion.value a r)

module RestrictedDiagramEvaluation {Γ : Context} {I C P Q : CAT Γ}
  (a : MAP One I) (h : MAP P (Fun I C)) (H : MAP (P × I) C)
  (beta : funUncurry h =₁ H) (r : MAP Q P) where
  private
    J : MAP (Q × I) (P × I)
    J = productMap r (id I)
    i : MAP Q (Q × I)
    i = insert a
    j : MAP P (P × I)
    j = insert a
    U : MAP (P × I) C
    U = funUncurry h
    module N = ParameterInsertion a
    module Native = UncurryParameter a h r
    E : funUncurry (h ∘ r) =₁ (U ∘ J)
    E = evaluate-restrict (funEval {C = I} {D = C}) h r
    old = AtPoint.uncurry-image a h
    new = AtPoint.uncurry-image a (h ∘ r)
    old-r = old ▷ r
    beta-r = (beta ▷ j) ▷ r
    beta-J = (beta ▷ J) ▷ i
    E-i = E ▷ i
    E-inverse-i = E ⁻¹ ▷ i
    raw-route = post-square-cell U i J j r (N.value r)
    A = comp-assoc i J U
    B = comp-assoc r j U
    step = U ◁ N.value r

  input-assoc = comp-assoc r h (evAt a)
  diagram-route = parameter-square-image {I = I} {C = C} {P = P} {Q = Q} a H r

  representation : funUncurry (h ∘ r) =₁ (H ∘ J)
  representation = represented-restriction {I = I} {C = C} {P = P} {Q = Q} h H beta r
  point : (evAt a ∘ (h ∘ r)) =₁ ((H ∘ J) ∘ i)
  point = (representation ▷ i) ∙ new
  original-point : (evAt a ∘ h) =₁ (H ∘ j)
  original-point = AtPoint.represented-point {I = I} {C = C} a h H beta

  private
    native-route : (new ∙ input-assoc) =₂ (E-inverse-i ∙ (raw-route ∙ old-r))
    native-route = comp₌-cong (id₌ E-inverse-i)
      (((comp₌-assoc (A ⁻¹) (step ∙ B) old-r) ⁻¹) ∙
        comp₌-cong (id₌ (A ⁻¹)) ((comp₌-assoc step B old-r) ⁻¹)) ∙ Native.composition
    representation-image : (representation ▷ i) =₂ (beta-J ∙ E-i)
    representation-image = preWhisker-comp₌ (beta ▷ J) E i
    cancel-evaluation : (E-i ∙ (E-inverse-i ∙ (raw-route ∙ old-r))) =₂ (raw-route ∙ old-r)
    cancel-evaluation = comp-inv-left E-i (raw-route ∙ old-r) ∙
      comp₌-cong (id₌ E-i) (comp₌-cong (preWhisker-inverse E i) (id₌ (raw-route ∙ old-r)))
    diagram-square : (beta-J ∙ raw-route) =₂ (diagram-route ∙ beta-r)
    diagram-square = (unconst-sides₌ (post-square-cell-outer i J j r (N.value r) beta)) ⁻¹

  compatibility : (point ∙ input-assoc) =₂ (diagram-route ∙ (original-point ▷ r))
  compatibility = comp₌-cong (id₌ diagram-route) ((preWhisker-comp₌ (beta ▷ j) old r) ⁻¹) ∙
    (comp₌-assoc diagram-route beta-r old-r ∙
      (comp₌-cong diagram-square (id₌ old-r) ∙
        (((comp₌-assoc beta-J raw-route old-r) ⁻¹) ∙
          (comp₌-cong (id₌ beta-J) cancel-evaluation ∙
            (comp₌-assoc beta-J E-i (E-inverse-i ∙ (raw-route ∙ old-r)) ∙
              (comp₌-cong representation-image (id₌ (E-inverse-i ∙ (raw-route ∙ old-r))) ∙
                (comp₌-cong (id₌ (representation ▷ i)) native-route ∙
                  comp₌-assoc (representation ▷ i) new input-assoc)))))))
```
