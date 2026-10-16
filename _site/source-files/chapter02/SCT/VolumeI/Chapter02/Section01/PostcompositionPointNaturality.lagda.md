# Postcomposition respects changes of an evaluated point

The specified comparison between point evaluation and postcomposition is
natural in an identification of points of the diagram shape. This is the
vertex identification needed when carrying the three corners of a triangle
through a functor. It is obtained by pasting the existing uncurrying square,
interchange for the original beta, and associator naturality.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PostcompositionPointNaturality where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc; interchange-fixedOuter)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (paste-square₌; replace-sides₌; unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (postWhisker-comp-One)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-β)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt; evAt-cong; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (evAt-post)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters using (module PointNaturality)

module PostcompositionPointNaturality {Γ : Context} {I C D : CAT Γ} (F : MAP C D) where
  private
    K : MAP (Fun I C) (Fun I D)
    K = funPost F
    e : MAP (Fun I C × I) C
    e = funEval
    module Point = PointNaturality K
    beta = funPost-β {C = I} F

    normalize : (a : MAP One I)
      → ((comp-assoc (insert a) e F ∙ (beta ▷ insert a)) ∙ AtPoint.uncurry-image a K) =₂ evAt-post a F
    normalize a = comp₌-assoc (comp-assoc (insert a) e F) (beta ▷ insert a) (AtPoint.uncurry-image a K)

  point-square : {a b : MAP One I} (alpha : a =₁ b)
    → SquareCell₌ (evAt-cong {C = D} alpha ▷ K) (F ◁ evAt-cong {C = C} alpha)
        (evAt-post a F) (evAt-post b F)
  point-square {a} {b} alpha = replace-sides₌ (normalize a) (normalize b)
    (paste-square₌ (Point.uncurry-point-square alpha)
      (paste-square₌
        (unconst-sides₌ (interchange-fixedOuter beta (Point.insertion-action alpha)))
        (postWhisker-comp-One (Point.insertion-action alpha) e F)))
```


Restriction to a categorical family retains the associators in the two
point comparisons. The resulting square is used at each vertex of the
postcomposed triangle family.

```agda
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (pre-square₌; inverse-square₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (preWhisker-comp-One; whisker-mixed-One)

module PostcompositionPointsAt {Γ : Context} {I P C D : CAT Γ}
  (F : MAP C D) (h : MAP P (Fun I C)) where
  private
    K = funPost {C = I} F
  point : (a : MAP One I) → (evAt a ∘ (K ∘ h)) =₁ (F ∘ (evAt a ∘ h))
  point a = comp-assoc h (evAt a) F ∙
    ((evAt-post a F ▷ h) ∙ (comp-assoc h K (evAt a)) ⁻¹)
  private
    normalize : (a : MAP One I)
      → ((comp-assoc h (evAt a) F ∙ (evAt-post a F ▷ h)) ∙
          (comp-assoc h K (evAt a)) ⁻¹) =₂ point a
    normalize a = comp₌-assoc (comp-assoc h (evAt a) F)
      (evAt-post a F ▷ h) ((comp-assoc h K (evAt a)) ⁻¹)
  point-square : {a b : MAP One I} (alpha : a =₁ b)
    → SquareCell₌ (evAt-cong {C = D} alpha ▷ (K ∘ h))
        (F ◁ (evAt-cong {C = C} alpha ▷ h)) (point a) (point b)
  point-square {a} {b} alpha = replace-sides₌ (normalize a) (normalize b)
    (paste-square₌ (inverse-square₌ (preWhisker-comp-One (evAt-cong {C = D} alpha) K h))
      (paste-square₌ (pre-square₌ h (PostcompositionPointNaturality.point-square F alpha))
        (whisker-mixed-One (evAt-cong {C = C} alpha) h F)))
```
