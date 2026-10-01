# Evaluated slice-arrow cones

The endpoint comparison identifies the entire evaluated cone with the
corresponding edge and fixed-vertex cone. In particular, its matching
is retained for the subsequent pullback cancellation argument.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceArrowTriangles as Presentations

import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEndpointMatchings as Matchings
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationCones as Evaluation
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.NormalizedMappedConeComparisons as Evaluated

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEndpointCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone; ConeIso; conePre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.QuotientComparisons 𝒯 using (quotient-comparison)
open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I
  using (module SliceEndpoint; module CosliceEndpoint)

module Slice {C : CAT} (x : Obj-abs C) where
  module Boundary = Matchings.Slice 𝒯 M ℱ P I E S Q x
  open Boundary using (t; b; δ; image; left-endpoint; right-endpoint;
    left-endpoint-normal; right-endpoint-normal; left-image; right-image; endpoint-square)
  module LeftFrame = Boundary.LeftFrame using (vertex)
  module LeftParameter = Boundary.LeftParameter using (boundary′)
  module PointFrame = Boundary.PointFrame using (point-frame)
  module Eval = Evaluation.EvaluationCone 𝒯 M ℱ P one ev₁ x
    using (normalized-cone; module Induced; module CoordinateEvaluation)
  module Source = SliceEndpoint x using (square; square-isPullback)
  module Arrows = Presentations.SliceAt 𝒯 M ℱ P I E S Q x using (forward; normalized-comparison; module AtEndpoint)
  module Endpoint = Evaluated.At 𝒯 M ℱ P one Source.square Arrows.forward
    image Arrows.normalized-comparison using (comparison)

  edge-cone : Cone ev₁ x Boundary.Presentation.category
  edge-cone = record { left = edge₀ ∘ t ; right = b ; match = δ ∙ LeftFrame.vertex }

  abstract
    framed-square :
      (((x ◁ PointFrame.point-frame) ∙ evaluate-post-at one x (Cone.right image)) ∙
        (ev₁ ◁ Cone.match image)) =₂
      ((δ ∙ LeftFrame.vertex) ∙ ((ev₁ ◁ LeftParameter.boundary′) ∙
        evaluate-post-at one ev₁ (Cone.left image)))
    framed-square =
      (isoComp-assoc-at δ LeftFrame.vertex
        ((ev₁ ◁ LeftParameter.boundary′) ∙ evaluate-post-at one ev₁ (Cone.left image))) ⁻¹ ∙
      (isoComp-cong (idIso δ) left-endpoint-normal ∙
      (endpoint-square left-endpoint right-endpoint left-image right-image ∙
        isoComp-cong (right-endpoint-normal ⁻¹) (idIso (ev₁ ◁ Cone.match image))))

    edge-coordinate-comparison : ConeIso (Eval.CoordinateEvaluation.read image) edge-cone
    edge-coordinate-comparison = quotient-comparison ev₁ x LeftParameter.boundary′ PointFrame.point-frame
      (evaluate-post-at one ev₁ (Cone.left image)) (evaluate-post-at one x (Cone.right image))
      (ev₁ ◁ Cone.match image) (δ ∙ LeftFrame.vertex) framed-square

    comparison : ConeIso (conePre (ev₁ ∘ Arrows.forward) Source.square) edge-cone
    comparison = coneIso-compose edge-coordinate-comparison Endpoint.comparison

    comparison-left : ConeIso.leftIso comparison =₂
      (LeftParameter.boundary′ ∙ ((ev₁ ◁ ConeIso.leftIso Arrows.normalized-comparison) ∙
        (evaluate-post-at one (Cone.left Source.square) Arrows.forward) ⁻¹))
    comparison-left = idIso _

module Coslice {C : CAT} (x : Obj-abs C) where
  module Boundary = Matchings.Coslice 𝒯 M ℱ P I E S Q x
  open Boundary using (t; b; δ; image; left-endpoint; right-endpoint;
    left-endpoint-normal; right-endpoint-normal; left-image; right-image; endpoint-square)
  module LeftFrame = Boundary.LeftFrame using (vertex)
  module LeftParameter = Boundary.LeftParameter using (boundary′)
  module PointFrame = Boundary.PointFrame using (point-frame)
  module Eval = Evaluation.EvaluationCone 𝒯 M ℱ P zero ev₀ x
    using (normalized-cone; module Induced; module CoordinateEvaluation)
  module Source = CosliceEndpoint x using (square; square-isPullback)
  module Arrows = Presentations.CosliceAt 𝒯 M ℱ P I E S Q x using (forward; normalized-comparison; module AtEndpoint)
  module Endpoint = Evaluated.At 𝒯 M ℱ P zero Source.square Arrows.forward
    image Arrows.normalized-comparison using (comparison)

  edge-cone : Cone ev₀ x Boundary.Presentation.category
  edge-cone = record { left = edge₂ ∘ t ; right = b ; match = δ ∙ LeftFrame.vertex }

  abstract
    framed-square :
      (((x ◁ PointFrame.point-frame) ∙ evaluate-post-at zero x (Cone.right image)) ∙
        (ev₀ ◁ Cone.match image)) =₂
      ((δ ∙ LeftFrame.vertex) ∙ ((ev₀ ◁ LeftParameter.boundary′) ∙
        evaluate-post-at zero ev₀ (Cone.left image)))
    framed-square =
      (isoComp-assoc-at δ LeftFrame.vertex
        ((ev₀ ◁ LeftParameter.boundary′) ∙ evaluate-post-at zero ev₀ (Cone.left image))) ⁻¹ ∙
      (isoComp-cong (idIso δ) left-endpoint-normal ∙
      (endpoint-square left-endpoint right-endpoint left-image right-image ∙
        isoComp-cong (right-endpoint-normal ⁻¹) (idIso (ev₀ ◁ Cone.match image))))

    edge-coordinate-comparison : ConeIso (Eval.CoordinateEvaluation.read image) edge-cone
    edge-coordinate-comparison = quotient-comparison ev₀ x LeftParameter.boundary′ PointFrame.point-frame
      (evaluate-post-at zero ev₀ (Cone.left image)) (evaluate-post-at zero x (Cone.right image))
      (ev₀ ◁ Cone.match image) (δ ∙ LeftFrame.vertex) framed-square

    comparison : ConeIso (conePre (ev₀ ∘ Arrows.forward) Source.square) edge-cone
    comparison = coneIso-compose edge-coordinate-comparison Endpoint.comparison

    comparison-left : ConeIso.leftIso comparison =₂
      (LeftParameter.boundary′ ∙ ((ev₀ ◁ ConeIso.leftIso Arrows.normalized-comparison) ∙
        (evaluate-post-at zero (Cone.left Source.square) Arrows.forward) ⁻¹))
    comparison-left = idIso _

```
