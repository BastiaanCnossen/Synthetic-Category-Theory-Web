# Currying a square with specified side comparisons

Double currying regards a square as a morphism in the arrow category.
Evaluation of its outer variable gives the vertical sides; postcomposition
by evaluation of the inner variable gives the horizontal sides. Reflection
constructs these identifications and retains their complete point images.

This module computes sides and their reflected point images. The comparison
between the two orders of evaluating a corner remains a separate obligation;
these declarations alone do not construct a FramedSquare.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCurrying where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; comp₌-assoc)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (prewhiskered-composite)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funCurry; funUncurry; funCurry-β)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPost; funPre-uncurry; funPost-uncurry)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; insert; evAt; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyReflection using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section02.SquareCoordinates using (coinsert; module SquareCoordinates)

open import SCT.VolumeI.Chapter01.Section07.DiagramRepresentations
  using (represented-postcomposition; represented-restriction)

module SquareCurrying {Γ : Context} {P C : CAT Γ} (sigma : MAP P (Fun ([1] × [1]) C)) where
  private
    I = [1] {Γ = Γ}
    module Coordinates = SquareCoordinates P
  diagram : MAP (P × (I × I)) C
  diagram = funUncurry {C = I × I} {D = C} sigma
  reordered : MAP ((P × I) × I) C
  reordered = diagram ∘ Coordinates.permute
  first-curry : MAP (P × I) (Ar C)
  first-curry = funCurry {C = I} {D = C} reordered
  nested : MAP P (Ar (Ar C))
  nested = funCurry {C = I} {D = Ar C} first-curry

  module Vertical (v : MAP One I) where
    private
      module Coordinate = Coordinates.Vertical v
    side : MAP P (Ar C)
    side = funPre {D = C} (insert {P = I} v) ∘ sigma
    restricted : MAP P (Ar C)
    restricted = first-curry ∘ insert v
    beta : funUncurry side =₁ (diagram ∘ Coordinate.restriction)
    beta = funPre-uncurry (insert {P = I} v) sigma
    representation-tail : funUncurry restricted =₁ (reordered ∘ Coordinate.step)
    representation-tail = represented-restriction {I = I} {C = C} {P = P × I} {Q = P}
      first-curry reordered (funCurry-β reordered) (insert {P = P} v)
    private
      axis-head : (diagram ∘ (Coordinates.permute ∘ Coordinate.step)) =₁ (diagram ∘ Coordinate.restriction)
      axis-head = diagram ◁ Coordinate.comparison
      axis-associator : (reordered ∘ Coordinate.step) =₁ (diagram ∘ (Coordinates.permute ∘ Coordinate.step))
      axis-associator = comp-assoc Coordinate.step Coordinates.permute diagram
    theta : funUncurry restricted =₁ (diagram ∘ Coordinate.restriction)
    theta = axis-head ∙ (axis-associator ∙ representation-tail)
    module Comparison = ReflectedEndpoint restricted side (diagram ∘ Coordinate.restriction) beta theta
    boundary : (evAt v ∘ nested) =₁ side
    boundary = Comparison.comparison ∙ AtPoint.curry-image v first-curry
    opaque
      representation-group : (x : MAP One I)
        → ((theta ▷ insert x) ∙ AtPoint.uncurry-image x restricted) =₂
          (((axis-head ∙ axis-associator) ▷ insert x) ∙
            ((representation-tail ▷ insert x) ∙ AtPoint.uncurry-image x restricted))
      representation-group x =
        prewhiskered-composite {X = One} {B = P} {C = P × I} {D = C}
          (insert x) (axis-head ∙ axis-associator) representation-tail
          (AtPoint.uncurry-image {I = I} {C = C} x restricted) ∙
        comp₌-cong
          (preWhisker (insert x) ◁ ((comp₌-assoc axis-head axis-associator representation-tail) ⁻¹))
          (id₌ (AtPoint.uncurry-image x restricted))

  module Horizontal (u : MAP One I) where
    private
      module Coordinate = Coordinates.Horizontal u
    side : MAP P (Ar C)
    side = funPre {D = C} (coinsert u) ∘ sigma
    evaluated : MAP P (Ar C)
    evaluated = funPost {C = I} (evAt {C = C} u) ∘ nested
    beta : funUncurry side =₁ (diagram ∘ Coordinate.restriction)
    beta = funPre-uncurry (coinsert u) sigma
    representation-tail : funUncurry evaluated =₁ (evAt u ∘ first-curry)
    representation-tail = represented-postcomposition {I = I} {P = P} {C = Ar C} {D = C}
      (evAt {C = C} u) nested first-curry (funCurry-β first-curry)
    private
      axis-head : (diagram ∘ (Coordinates.permute ∘ Coordinate.step)) =₁ (diagram ∘ Coordinate.restriction)
      axis-head = diagram ◁ Coordinate.comparison
      axis-associator : (reordered ∘ Coordinate.step) =₁ (diagram ∘ (Coordinates.permute ∘ Coordinate.step))
      axis-associator = comp-assoc Coordinate.step Coordinates.permute diagram
      curry-point : (evAt u ∘ first-curry) =₁ (reordered ∘ Coordinate.step)
      curry-point = AtPoint.curry-image u reordered
    theta : funUncurry evaluated =₁ (diagram ∘ Coordinate.restriction)
    theta = axis-head ∙ (axis-associator ∙ (curry-point ∙ representation-tail))
    module Comparison = ReflectedEndpoint evaluated side (diagram ∘ Coordinate.restriction) beta theta
    comparison : evaluated =₁ side
    comparison = Comparison.comparison
    opaque
      representation-group : (x : MAP One I)
        → ((theta ▷ insert x) ∙ AtPoint.uncurry-image x evaluated) =₂
          (((axis-head ∙ axis-associator) ▷ insert x) ∙
            (((curry-point ∙ representation-tail) ▷ insert x) ∙ AtPoint.uncurry-image x evaluated))
      representation-group x =
        prewhiskered-composite {X = One} {B = P} {C = P × I} {D = C}
          (insert x) (axis-head ∙ axis-associator) (curry-point ∙ representation-tail)
          (AtPoint.uncurry-image {I = I} {C = C} x evaluated) ∙
        comp₌-cong
          (preWhisker (insert x) ◁ ((comp₌-assoc axis-head axis-associator (curry-point ∙ representation-tail)) ⁻¹))
          (id₌ (AtPoint.uncurry-image x evaluated))
```
