# The matching square over a fixed triangle vertex

The normalized image cone of the slice-arrow presentation has a quotient
matching. Its two comparison maps to identity arrows form a specified
square over the vertex-fiber matching. Retraction along evaluation takes
this entire square to its endpoint square.

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
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.NormalizedSliceTriangles as Normalized
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceArrowTriangles as Presentations
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceArrowSquares as SquarePresentations
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.SplitRetractionMatching as Retractions
import SCT.VolumeI.Chapter01.Section06.Coordinates.PointFrameRestriction as PointFrames
import SCT.VolumeI.Chapter01.Section06.Coordinates.FramedProjectionRestriction as Framed

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEndpointMatchings
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone; conePre)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectionRestriction 𝒯
  using (restricted-normalization; normalization-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.QuotientComparisons 𝒯
  using (nested-quotient-square)

module Slice {C : CAT} (x : Obj-abs C) where
  module Triangle = Normalized.Slice 𝒯 M ℱ P I E S Q x
    using (square; square-isPullback; k; nested; edge; vertex; full-matching; evaluation-endpoint; full-image)
  module Presentation = Presentations.Vertex 𝒯 M ℱ P I E S Q x one
    Triangle.square Triangle.square-isPullback using (category; module Image)
  module EndpointRetraction = Retractions.WithRetraction 𝒯 (identityArrow {C}) ev₁ identity-target
    using (frame; retract-square; image-nested-restrict; image-two-step-restrict)
  module Constants = SquarePresentations.Endpoint 𝒯 M ℱ P I C one x
    using (constant-endpoint; nested; side; side-comparison; module ConstantMatching)

  point = pullbackCone (evaluate {C = C} vertex₂) x
  t = Cone.left point
  b = Cone.right point
  δ = Cone.match point
  restricted = conePre t Triangle.square
  image = Presentation.Image.simplified

  left-matching : (funPost ev₁ ∘ Cone.left image) =₁ (identityArrow ∘ (evaluate vertex₂ ∘ t))
  left-matching = Cone.match restricted ∙ Presentation.Image.L.forward

  right-matching : (funPost x ∘ Cone.right image) =₁ (identityArrow ∘ (x ∘ b))
  right-matching = comp-assoc b x identityArrow ∙ Presentation.Image.R.forward

  right-endpoint : (ev₁ ∘ (funPost x ∘ Cone.right image)) =₁ (x ∘ b)
  right-endpoint = restricted-normalization ev₁ (funPost x) (constantDiagram [1] One)
    Constants.constant-endpoint b

  left-endpoint : (ev₁ ∘ (funPost ev₁ ∘ Cone.left image)) =₁ (evaluate vertex₂ ∘ t)
  left-endpoint = restricted-normalization ev₁ (funPost ev₁) Triangle.nested
    Triangle.evaluation-endpoint t ∙ (ev₁ ◁ (funPost ev₁ ◁ comp-assoc t Triangle.k Constants.nested)) ⁻¹

  module PointFrame = PointFrames.At.Restrict 𝒯 ev₁ (funPost x) ev₁ x
    (evaluate-post one x) (constantDiagram [1] One) (evaluate-constant one) b
    using (point-frame; comparison)
  module LeftFrame = Framed.At.Restrict 𝒯 ev₁ (funPost ev₁) ev₁ ev₁
    (evaluate-post one ev₁) Triangle.nested Triangle.edge Triangle.vertex t
    using (vertex; module AtParameter)
  module LeftParameter = LeftFrame.AtParameter (comp-assoc t Triangle.k Constants.nested)
    using (boundary′; changed-comparison)

  abstract
    left-endpoint-normal : left-endpoint =₂
      (LeftFrame.vertex ∙ ((ev₁ ◁ LeftParameter.boundary′) ∙
        evaluate-post-at one ev₁ (Cone.left image)))
    left-endpoint-normal = LeftParameter.changed-comparison

    left-matching-normal : left-matching =₂
      (comp-assoc t (evaluate vertex₂) identityArrow ∙
        restricted-normalization (funPost ev₁) Constants.nested Triangle.k Triangle.full-matching t)
    left-matching-normal = isoComp-cong (idIso (comp-assoc t (evaluate vertex₂) identityArrow))
      ((normalization-pre (funPost ev₁) Constants.nested Constants.side Constants.side-comparison
        Triangle.k t (Cone.match Triangle.square)) ⁻¹) ∙
      isoComp-assoc-at (comp-assoc t (evaluate vertex₂) identityArrow)
        ((Cone.match Triangle.square ▷ t) ∙ (comp-assoc t Triangle.k Constants.side) ⁻¹)
        Presentation.Image.L.forward

    left-image : (EndpointRetraction.frame (evaluate vertex₂ ∘ t) ∙ (ev₁ ◁ left-matching)) =₂ left-endpoint
    left-image = EndpointRetraction.image-two-step-restrict (funPost ev₁) Constants.nested Triangle.k
      Triangle.full-matching Triangle.evaluation-endpoint t Triangle.full-image ∙
      isoComp-cong (idIso (EndpointRetraction.frame (evaluate vertex₂ ∘ t)))
        (postWhisker ev₁ ◁ left-matching-normal)

    right-endpoint-normal : right-endpoint =₂
      ((x ◁ PointFrame.point-frame) ∙ evaluate-post-at one x (Cone.right image))
    right-endpoint-normal = PointFrame.comparison

    right-image : (EndpointRetraction.frame (x ∘ b) ∙ (ev₁ ◁ right-matching)) =₂ right-endpoint
    right-image = EndpointRetraction.image-nested-restrict (funPost x) (constantDiagram [1] One)
      Constants.ConstantMatching.matching Constants.constant-endpoint b Constants.ConstantMatching.image-law

    matching-square : (right-matching ∙ Cone.match image) =₂
      ((identityArrow ◁ δ) ∙ left-matching)
    matching-square = nested-quotient-square Presentation.Image.L.forward (Cone.match restricted)
      (identityArrow ◁ δ) (comp-assoc b x identityArrow) Presentation.Image.R.forward

    endpoint-square :
      (p : (ev₁ ∘ (funPost ev₁ ∘ Cone.left image)) =₁ (evaluate vertex₂ ∘ t))
      (q : (ev₁ ∘ (funPost x ∘ Cone.right image)) =₁ (x ∘ b)) →
      (EndpointRetraction.frame (evaluate vertex₂ ∘ t) ∙ (ev₁ ◁ left-matching)) =₂ p →
      (EndpointRetraction.frame (x ∘ b) ∙ (ev₁ ◁ right-matching)) =₂ q →
      (q ∙ (ev₁ ◁ Cone.match image)) =₂ (δ ∙ p)
    endpoint-square p q left right = EndpointRetraction.retract-square left-matching right-matching
      (Cone.match image) δ p q matching-square left right

module Coslice {C : CAT} (x : Obj-abs C) where
  module Triangle = Normalized.Coslice 𝒯 M ℱ P I E S Q x
    using (square; square-isPullback; k; nested; edge; vertex; full-matching; evaluation-endpoint; full-image)
  module Presentation = Presentations.Vertex 𝒯 M ℱ P I E S Q x zero
    Triangle.square Triangle.square-isPullback using (category; module Image)
  module EndpointRetraction = Retractions.WithRetraction 𝒯 (identityArrow {C}) ev₀ identity-source
    using (frame; retract-square; image-nested-restrict; image-two-step-restrict)
  module Constants = SquarePresentations.Endpoint 𝒯 M ℱ P I C zero x
    using (constant-endpoint; nested; side; side-comparison; module ConstantMatching)

  point = pullbackCone (evaluate {C = C} vertex₀) x
  t = Cone.left point
  b = Cone.right point
  δ = Cone.match point
  restricted = conePre t Triangle.square
  image = Presentation.Image.simplified

  left-matching : (funPost ev₀ ∘ Cone.left image) =₁ (identityArrow ∘ (evaluate vertex₀ ∘ t))
  left-matching = Cone.match restricted ∙ Presentation.Image.L.forward

  right-matching : (funPost x ∘ Cone.right image) =₁ (identityArrow ∘ (x ∘ b))
  right-matching = comp-assoc b x identityArrow ∙ Presentation.Image.R.forward

  right-endpoint : (ev₀ ∘ (funPost x ∘ Cone.right image)) =₁ (x ∘ b)
  right-endpoint = restricted-normalization ev₀ (funPost x) (constantDiagram [1] One)
    Constants.constant-endpoint b

  left-endpoint : (ev₀ ∘ (funPost ev₀ ∘ Cone.left image)) =₁ (evaluate vertex₀ ∘ t)
  left-endpoint = restricted-normalization ev₀ (funPost ev₀) Triangle.nested
    Triangle.evaluation-endpoint t ∙ (ev₀ ◁ (funPost ev₀ ◁ comp-assoc t Triangle.k Constants.nested)) ⁻¹

  module PointFrame = PointFrames.At.Restrict 𝒯 ev₀ (funPost x) ev₀ x
    (evaluate-post zero x) (constantDiagram [1] One) (evaluate-constant zero) b
    using (point-frame; comparison)
  module LeftFrame = Framed.At.Restrict 𝒯 ev₀ (funPost ev₀) ev₀ ev₀
    (evaluate-post zero ev₀) Triangle.nested Triangle.edge Triangle.vertex t
    using (vertex; module AtParameter)
  module LeftParameter = LeftFrame.AtParameter (comp-assoc t Triangle.k Constants.nested)
    using (boundary′; changed-comparison)

  abstract
    left-endpoint-normal : left-endpoint =₂
      (LeftFrame.vertex ∙ ((ev₀ ◁ LeftParameter.boundary′) ∙
        evaluate-post-at zero ev₀ (Cone.left image)))
    left-endpoint-normal = LeftParameter.changed-comparison

    left-matching-normal : left-matching =₂
      (comp-assoc t (evaluate vertex₀) identityArrow ∙
        restricted-normalization (funPost ev₀) Constants.nested Triangle.k Triangle.full-matching t)
    left-matching-normal = isoComp-cong (idIso (comp-assoc t (evaluate vertex₀) identityArrow))
      ((normalization-pre (funPost ev₀) Constants.nested Constants.side Constants.side-comparison
        Triangle.k t (Cone.match Triangle.square)) ⁻¹) ∙
      isoComp-assoc-at (comp-assoc t (evaluate vertex₀) identityArrow)
        ((Cone.match Triangle.square ▷ t) ∙ (comp-assoc t Triangle.k Constants.side) ⁻¹)
        Presentation.Image.L.forward

    left-image : (EndpointRetraction.frame (evaluate vertex₀ ∘ t) ∙ (ev₀ ◁ left-matching)) =₂ left-endpoint
    left-image = EndpointRetraction.image-two-step-restrict (funPost ev₀) Constants.nested Triangle.k
      Triangle.full-matching Triangle.evaluation-endpoint t Triangle.full-image ∙
      isoComp-cong (idIso (EndpointRetraction.frame (evaluate vertex₀ ∘ t)))
        (postWhisker ev₀ ◁ left-matching-normal)

    right-endpoint-normal : right-endpoint =₂
      ((x ◁ PointFrame.point-frame) ∙ evaluate-post-at zero x (Cone.right image))
    right-endpoint-normal = PointFrame.comparison

    right-image : (EndpointRetraction.frame (x ∘ b) ∙ (ev₀ ◁ right-matching)) =₂ right-endpoint
    right-image = EndpointRetraction.image-nested-restrict (funPost x) (constantDiagram [1] One)
      Constants.ConstantMatching.matching Constants.constant-endpoint b Constants.ConstantMatching.image-law

    matching-square : (right-matching ∙ Cone.match image) =₂
      ((identityArrow ◁ δ) ∙ left-matching)
    matching-square = nested-quotient-square Presentation.Image.L.forward (Cone.match restricted)
      (identityArrow ◁ δ) (comp-assoc b x identityArrow) Presentation.Image.R.forward

    endpoint-square :
      (p : (ev₀ ∘ (funPost ev₀ ∘ Cone.left image)) =₁ (evaluate vertex₀ ∘ t))
      (q : (ev₀ ∘ (funPost x ∘ Cone.right image)) =₁ (x ∘ b)) →
      (EndpointRetraction.frame (evaluate vertex₀ ∘ t) ∙ (ev₀ ◁ left-matching)) =₂ p →
      (EndpointRetraction.frame (x ∘ b) ∙ (ev₀ ◁ right-matching)) =₂ q →
      (q ∙ (ev₀ ◁ Cone.match image)) =₂ (δ ∙ p)
    endpoint-square p q left right = EndpointRetraction.retract-square left-matching right-matching
      (Cone.match image) δ p q matching-square left right
```
