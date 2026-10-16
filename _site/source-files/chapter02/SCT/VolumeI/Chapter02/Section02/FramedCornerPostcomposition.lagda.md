# Transporting a framed corner through a functor

A comparison from the two diagram edges to framed arrow families carries a
corner to the matching prescribed by their common endpoint. Postcomposition
preserves this entire square. The proof pastes the native corner comparison
with the functor image of the given square, then cancels the point-evaluation
frames. No matching witness is replaced.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.FramedCornerPostcomposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; postWhisker-comp₌; inv-comp-left)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (paste-square₌; inverse-square₌; transpose-square₌; post-square₌; replace-sides₌; replace-edges₌; inv-comp-square₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (postWhisker-inverse; comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (postWhisker-comp-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-change-square-One)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPost)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; evAt)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (evAt-post)
open import SCT.VolumeI.Chapter02.Section01.PostcompositionPointNaturality using (module PostcompositionPointsAt)
open import SCT.VolumeI.Chapter02.Section02.PostcompositionCorners using (module PostcompositionCorner)

private
  module EvaluationInputs {Γ : Context} {P C D : CAT Γ}
    (F : MAP C D) (a : MAP One ([1] {Γ = Γ})) {h k : MAP P (Ar C)} (delta : h =₁ k) where
    compatibility : SquareCell₌ (evAt {C = D} a ◁ (funPost F ◁ delta))
      (F ◁ (evAt {C = C} a ◁ delta))
      (PostcompositionPointsAt.point F h a) (PostcompositionPointsAt.point F k a)
    compatibility = paste-square₌
      (restrict-change-square-One (evAt a) (funPost F) (F ∘ evAt a) (evAt-post a F) delta)
      (postWhisker-comp-One delta (evAt a) F)

module FramedCornerImage {Γ : Context} {J P C D : CAT Γ}
  (F : MAP C D) (u v : MAP One ([1] {Γ = Γ})) (d k : MAP [1] J)
  (delta : (d ∘ u) =₁ (k ∘ v)) (sigma : MAP P (Fun J C))
  (h l : MAP P (Ar C)) {x : MAP P C}
  (a : (evAt u ∘ h) =₁ x) (b : (evAt v ∘ l) =₁ x)
  (first : (funPre d ∘ sigma) =₁ h) (second : (funPre k ∘ sigma) =₁ l) where
  module Native = PostcompositionCorner F u v d k delta sigma
  private
    K = funPost {C = [1]} F
    lp = PostcompositionPointsAt.point F (funPre d ∘ sigma) u
    rp = PostcompositionPointsAt.point F (funPre k ∘ sigma) v
    lh = PostcompositionPointsAt.point F h u
    rl = PostcompositionPointsAt.point F l v
    e = Native.LeftEdge.comparison
    f = Native.RightEdge.comparison
    ca = evAt {C = D} u ◁ e
    cb = evAt {C = D} v ◁ f
    fa = F ◁ (evAt {C = C} u ◁ first)
    fb = F ◁ (evAt {C = C} v ◁ second)
  first-image : (funPre {D = D} d ∘ (funPost F ∘ sigma)) =₁ (K ∘ h)
  first-image = (K ◁ first) ∙ e
  second-image : (funPre {D = D} k ∘ (funPost F ∘ sigma)) =₁ (K ∘ l)
  second-image = (K ◁ second) ∙ f
  source-frame = (F ◁ a) ∙ lh
  target-frame = (F ◁ b) ∙ rl

  private
    normalize-left : (fa ∙ (lp ∙ ca)) =₂ (lh ∙ (evAt u ◁ first-image))
    normalize-left = comp₌-cong (id₌ lh) ((postWhisker-comp₌ (evAt u) (K ◁ first) e) ⁻¹) ∙
      (comp₌-assoc lh (evAt u ◁ (K ◁ first)) ca ∙
        (comp₌-cong ((EvaluationInputs.compatibility F u first) ⁻¹) (id₌ ca) ∙
          (comp₌-assoc fa lp ca) ⁻¹))
    normalize-right : (fb ∙ (rp ∙ cb)) =₂ (rl ∙ (evAt v ◁ second-image))
    normalize-right = comp₌-cong (id₌ rl) ((postWhisker-comp₌ (evAt v) (K ◁ second) f) ⁻¹) ∙
      (comp₌-assoc rl (evAt v ◁ (K ◁ second)) cb ∙
        (comp₌-cong ((EvaluationInputs.compatibility F v second) ⁻¹) (id₌ cb) ∙
          (comp₌-assoc fb rp cb) ⁻¹))
    quotient = (b ⁻¹) ∙ a
    quotient-image : (F ◁ quotient) =₂ (((F ◁ b) ⁻¹) ∙ (F ◁ a))
    quotient-image = comp₌-cong (postWhisker-inverse F b) (id₌ (F ◁ a)) ∙
      postWhisker-comp₌ F (b ⁻¹) a
    frame-square : SquareCell₌ ((target-frame ⁻¹) ∙ source-frame) (F ◁ quotient) lh rl
    frame-square = replace-edges₌ (id₌ _) (quotient-image ⁻¹)
      (inv-comp-square₌ (comp₌-unitˡ-One source-frame) (comp₌-unitˡ-One target-frame))

  compatibility :
    SquareCell₌ (evAt u ◁ first) (evAt v ◁ second) Native.Before.matching quotient
    → SquareCell₌ (evAt u ◁ first-image) (evAt v ◁ second-image)
        Native.After.matching ((target-frame ⁻¹) ∙ source-frame)
  compatibility given = transpose-square₌
    (replace-sides₌ (inv-comp-left lh (evAt u ◁ first-image))
      (inv-comp-left rl (evAt v ◁ second-image))
      (paste-square₌
        (replace-sides₌ normalize-left normalize-right
          (paste-square₌ Native.compatibility (post-square₌ F (transpose-square₌ given))))
        (inverse-square₌ frame-square)))
```
