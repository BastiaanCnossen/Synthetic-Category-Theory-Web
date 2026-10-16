# A functor transports the matching at a diagram corner

A corner consists of two interval edges and a specified identification of
their meeting points. Restriction to a diagram family retains the original
matching. The reflected comparisons between restricting and postcomposing
the two edges form a square over the functor image of that matching.
The same statement covers the middle and both outer corners of a triangle.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.PostcompositionCorners where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; comp-inv-left; inv-comp-left; preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (paste-square₌; inverse-square₌; post-square₌; replace-sides₌)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; cone-restrict)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPost)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; evAt; evAt-pre; evAt-cong)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module CornerRestriction)
open import SCT.VolumeI.Chapter02.Section01.PostcompositionRestriction using (module PostRestriction)
open import SCT.VolumeI.Chapter02.Section01.PostcompositionPointNaturality using (module PostcompositionPointsAt)

module CornerRoutes {Γ : Context} {J P : CAT Γ} (C : CAT Γ)
  (u v : MAP One ([1] {Γ = Γ})) (d k : MAP [1] J)
  (delta : (d ∘ u) =₁ (k ∘ v)) (sigma : MAP P (Fun J C)) where
  private
    p = evAt-pre {C = C} u d
    q = evAt-pre {C = C} v k
    point = evAt-cong {C = C} delta
  cone : Cone (evAt {C = C} u) (evAt v) (Fun J C)
  cone = record { left = funPre d; right = funPre k; match = q ⁻¹ ∙ (point ∙ p) }
  left-route : (evAt u ∘ (funPre d ∘ sigma)) =₁ (evAt (d ∘ u) ∘ sigma)
  left-route = (p ▷ sigma) ∙ (comp-assoc sigma (funPre d) (evAt u)) ⁻¹
  right-route : (evAt v ∘ (funPre k ∘ sigma)) =₁ (evAt (k ∘ v) ∘ sigma)
  right-route = (q ▷ sigma) ∙ (comp-assoc sigma (funPre k) (evAt v)) ⁻¹
  matching = Cone.match (cone-restrict sigma cone)
  private
    module Restriction = CornerRestriction (evAt u) (evAt v) cone (point ∙ p) q
      (comp-inv-left q (point ∙ p)) sigma
    normalize : Restriction.left-frame =₂ ((point ▷ sigma) ∙ left-route)
    normalize = comp₌-assoc (point ▷ sigma) (p ▷ sigma)
        ((comp-assoc sigma (funPre d) (evAt u)) ⁻¹) ∙
      comp₌-cong (preWhisker-comp₌ point p sigma)
        (id₌ ((comp-assoc sigma (funPre d) (evAt u)) ⁻¹))
  compatibility : SquareCell₌ matching (point ▷ sigma) left-route right-route
  compatibility = normalize ∙ Restriction.compatibility

module PostcompositionCorner {Γ : Context} {J P C D : CAT Γ}
  (F : MAP C D) (u v : MAP One ([1] {Γ = Γ})) (d k : MAP [1] J)
  (delta : (d ∘ u) =₁ (k ∘ v)) (sigma : MAP P (Fun J C)) where
  module Before = CornerRoutes C u v d k delta sigma
  module After = CornerRoutes D u v d k delta (funPost F ∘ sigma)
  module LeftEdge = PostRestriction F d sigma
  module RightEdge = PostRestriction F k sigma
  private
    module Point = PostcompositionPointsAt F sigma
    module LeftPoint = PostcompositionPointsAt F (funPre {D = C} d ∘ sigma)
    module RightPoint = PostcompositionPointsAt F (funPre {D = C} k ∘ sigma)
    module Left = LeftEdge.At u
    module Right = RightEdge.At v
    fa = F ◁ Before.left-route
    fb = F ◁ Before.right-route
    x = evAt {C = D} u ◁ LeftEdge.comparison
    y = evAt {C = D} v ◁ RightEdge.comparison
    la = LeftPoint.point u
    rb = RightPoint.point v
    raw = paste-square₌
      (paste-square₌ After.compatibility (Point.point-square delta))
      (inverse-square₌ (post-square₌ F Before.compatibility))
    left-normal : ((fa ⁻¹) ∙ (Point.point (d ∘ u) ∙ After.left-route)) =₂ (la ∙ x)
    left-normal = inv-comp-left fa (la ∙ x) ∙
      comp₌-cong (id₌ (fa ⁻¹)) (comp₌-assoc fa la x ∙ Left.compatibility ⁻¹)
    right-normal : ((fb ⁻¹) ∙ (Point.point (k ∘ v) ∙ After.right-route)) =₂ (rb ∙ y)
    right-normal = inv-comp-left fb (rb ∙ y) ∙
      comp₌-cong (id₌ (fb ⁻¹)) (comp₌-assoc fb rb y ∙ Right.compatibility ⁻¹)

  compatibility : SquareCell₌ After.matching (F ◁ Before.matching)
    (LeftPoint.point u ∙ (evAt u ◁ LeftEdge.comparison))
    (RightPoint.point v ∙ (evAt v ◁ RightEdge.comparison))
  compatibility = replace-sides₌ left-normal right-normal raw
```
