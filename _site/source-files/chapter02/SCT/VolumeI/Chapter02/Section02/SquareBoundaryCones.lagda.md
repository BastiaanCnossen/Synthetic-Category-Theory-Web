# Complete geometric corner transfers

This draft starts with the common diagram-to-endpoint computation used by
both legs of each complete corner comparison. Its chosen diagram leg and
vertex route are shared. All six packings use the proved lower-diagonal
image from the same complete beta. The public Complete interface has no
additional compatibility premise.
The generic point calculations are reused from the preserved supporting
source, without importing any prescribed-edge or reflected-family owner.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareBoundaryCones where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc; comp₌-cong)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-right)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction using (product-restriction; restriction-compositor)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle using ([2])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt)
open import SCT.VolumeI.Chapter02.Section02.FramedDiagramTransport
  using (module InsertionPoints; module LiftedVertexSquare; module RestrictedVertexRepresentation;
    module DiagramVertexTransport; module VertexComparison; module VertexTransfer; module DecodedEndpointImage)

open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section06.Cones using (cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.FramedConeTransport using (module Corner)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using (zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using (d₀; d₁; d₂; vertex₀; vertex₁; vertex₂; d₂-zero; d₂-one; d₀-zero; d₀-one; d₁-zero; d₁-one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (MorphismFamily; ev₀; ev₁; evAt-pre; evAt-cong)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (triangle-cone; triangle-junction-vertex)
open import SCT.VolumeI.Chapter02.Section01.SquareGluing using (j₀; j₁; diagonal; j₀-d₂; j₀-d₀; j₁-d₂; j₁-d₀; j₀-diagonal; j₁-diagonal; j₀-vertex₀; j₀-vertex₁; j₀-vertex₂; j₁-vertex₀; j₁-vertex₁; j₁-vertex₂)
open import SCT.VolumeI.Chapter02.Section02.SquareCoordinates using (coinsert)
open import SCT.VolumeI.Chapter02.Section02.SquareCorners using (module SquareCorner)
open import SCT.VolumeI.Chapter02.Section02.SquareVertexShapes using (module At)
open import SCT.VolumeI.Chapter02.Section02.OriginalTriangleBoundaryComparisons using (module Boundaries)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations using (TrianglePresentation)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module CornerRestriction; module TriangleCornerFrames)

import SCT.VolumeI.Chapter02.Section02.CommonDiagramDiagonal as CommonDiagonal

module Endpoint {Γ : Context} {P C : CAT Γ}
  (sigma : MAP P (Fun ([1] × [1]) C))
  (triangle : MAP P (Fun [2] C))
  (j : MAP [2] ([1] × [1]))
  (leg : (funUncurry sigma ∘ product-restriction {P = P} j) =₁ funUncurry triangle)
  (d : MAP [1] [2]) (r : MAP [1] ([1] × [1]))
  (shape : (j ∘ d) =₁ r)
  (point : MAP One [1]) (triangle-vertex : MAP One [2])
  (square-vertex : MAP One ([1] × [1]))
  (face-vertex : (d ∘ point) =₁ triangle-vertex)
  (inclusion-vertex : (j ∘ triangle-vertex) =₁ square-vertex)
  (side-vertex : (r ∘ point) =₁ square-vertex)
  (shape-square :
    (inclusion-vertex ∙ ((j ◁ face-vertex) ∙ comp-assoc point d j)) =₂
      (side-vertex ∙ (shape ▷ point))) where
  module Source = RestrictedVertexRepresentation sigma r point square-vertex side-vertex
  module Target = RestrictedVertexRepresentation triangle d point triangle-vertex face-vertex
  private
    module Points = InsertionPoints P
    module Lift = LiftedVertexSquare P d j r point triangle-vertex square-vertex
      shape face-vertex inclusion-vertex side-vertex shape-square
    axis = productMap-cong (id₌ (id P)) shape ∙ restriction-compositor d j
  module Vertex = DiagramVertexTransport (product-restriction {P = P} j)
    (insert triangle-vertex) (insert square-vertex)
    (Points.action inclusion-vertex ∙ Source.Shape.χ j triangle-vertex)
    (funUncurry sigma) (funUncurry triangle) leg
  private
    input-square = (comp₌-assoc Lift.kappa-action Lift.axis-insertion Lift.axis-at) ⁻¹ ∙
      (Lift.compatibility ∙
        comp₌-assoc Lift.nu-action Lift.vertex-insertion (Lift.delta-face ∙ Lift.input-assoc))
  module Restriction = Vertex.Restriction (product-restriction {P = P} d)
    (product-restriction r) (insert point) axis
    (Points.action face-vertex ∙ Source.Shape.χ d point)
    (Points.action side-vertex ∙ Source.Shape.χ r point) input-square
  module Represented = Restriction.Represented Source.beta Target.beta
  module Change = VertexComparison Source.mu Target.mu Vertex.Zroute

  vertex : (evAt {C = C} square-vertex ∘ sigma) =₁ (evAt triangle-vertex ∘ triangle)
  vertex = Change.value

  module WithComparison
    (comparison : Source.side =₁ Target.side)
    (image : evaluate-cong (funEval {C = [1]} {D = C}) comparison =₂ Represented.raw) where
    private
      module Transfer = VertexTransfer Source.mu Target.mu Source.decoded-frame Target.decoded-frame
        Represented.expanded-at Source.represented-route Target.represented-route Vertex.Zroute
        vertex Change.image Source.route-compatibility Target.route-compatibility Represented.transfer
      module Decoded = DecodedEndpointImage Source.side Target.side point comparison Target.frame

      decoded : (Target.decoded-frame ∙ Decoded.diagram-endpoint) =₂
        (vertex ∙ Source.decoded-frame)
      decoded = Transfer.compatibility ∙
        (comp₌-cong (id₌ Target.decoded-frame)
          (preWhisker (insert point) ◁ (Represented.expanded-image ⁻¹)) ∙
            comp₌-cong (id₌ Target.decoded-frame) (preWhisker (insert point) ◁ image))

    compatible : (Target.frame ∙ (evAt point ◁ comparison)) =₂ (vertex ∙ Source.frame)
    compatible = cancel-right (Source.u ⁻¹)
      ((comp₌-assoc vertex Source.frame (Source.u ⁻¹)) ⁻¹ ∙
        (decoded ∙ (Decoded.compatibility ⁻¹)))

module Six {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C}
  {top : MorphismFamily x y} {right : MorphismFamily y z}
  {left : MorphismFamily x w} {bottom : MorphismFamily w z}
  {long : MorphismFamily x z}
  (given-upper : TrianglePresentation top right long)
  (given-lower : TrianglePresentation left bottom long) where
  module Sides = Boundaries given-upper given-lower
  module Shapes = At {Γ = Γ}
  module Frames = TriangleCornerFrames C
  module UpperJunction = CornerRestriction ev₁ ev₀ (triangle-cone C)
    (evAt-cong d₂-one ∙ evAt-pre one d₂)
    (evAt-cong d₀-zero ∙ evAt-pre zero d₀) (triangle-junction-vertex C) Sides.A.triangle
  module LowerJunction = CornerRestriction ev₁ ev₀ (triangle-cone C)
    (evAt-cong d₂-one ∙ evAt-pre one d₂)
    (evAt-cong d₀-zero ∙ evAt-pre zero d₀) (triangle-junction-vertex C) Sides.B.triangle
  module UpperSourceFrames = Frames.Source Sides.A.triangle
  module LowerSourceFrames = Frames.Source Sides.B.triangle
  module UpperTargetFrames = Frames.Target Sides.A.triangle
  module LowerTargetFrames = Frames.Target Sides.B.triangle

  -- This exact image is supplied by the complete native diagram-beta bridge.
  -- The final owner must instantiate it with that proof, not a new premise.
  module WithLowerDiagonalImage
    (lower-image : evaluate-cong (funEval {C = [1]} {D = C}) Sides.lower-diagonal =₂
      Sides.LowerDiagonalRoute.diagram-comparison) where
    module TopSource = Endpoint Sides.G.square Sides.A.triangle j₀ Sides.upper-diagram-leg
      d₂ (coinsert zero) j₀-d₂ zero vertex₀ (SquareCorner.vertex zero zero)
      d₂-zero j₀-vertex₀ (SquareCorner.horizontal-vertex zero zero) Shapes.UpperFirstSource.comparison
    module TopSourceComparison = TopSource.WithComparison Sides.Top.comparison Sides.Top.image
    module TopTarget = Endpoint Sides.G.square Sides.A.triangle j₀ Sides.upper-diagram-leg
      d₂ (coinsert zero) j₀-d₂ one vertex₁ (SquareCorner.vertex zero one)
      d₂-one j₀-vertex₁ (SquareCorner.horizontal-vertex zero one) Shapes.UpperFirstTarget.comparison
    module TopTargetComparison = TopTarget.WithComparison Sides.Top.comparison Sides.Top.image
    module RightSource = Endpoint Sides.G.square Sides.A.triangle j₀ Sides.upper-diagram-leg
      d₀ (insert one) j₀-d₀ zero vertex₁ (SquareCorner.vertex zero one)
      d₀-zero j₀-vertex₁ (SquareCorner.vertical-vertex zero one) Shapes.UpperSecondSource.comparison
    module RightSourceComparison = RightSource.WithComparison Sides.Right.comparison Sides.Right.image
    module RightTarget = Endpoint Sides.G.square Sides.A.triangle j₀ Sides.upper-diagram-leg
      d₀ (insert one) j₀-d₀ one vertex₂ (SquareCorner.vertex one one)
      d₀-one j₀-vertex₂ (SquareCorner.vertical-vertex one one) Shapes.UpperSecondTarget.comparison
    module RightTargetComparison = RightTarget.WithComparison Sides.Right.comparison Sides.Right.image
    module UpperDiagonalSource = Endpoint Sides.G.square Sides.A.triangle j₀ Sides.upper-diagram-leg
      d₁ diagonal j₀-diagonal zero vertex₀ (SquareCorner.vertex zero zero)
      d₁-zero j₀-vertex₀ (Shapes.diagonal-vertex zero) Shapes.UpperDiagonalSource.comparison
    module UpperDiagonalSourceComparison = UpperDiagonalSource.WithComparison Sides.UpperDiagonal.comparison Sides.UpperDiagonal.image
    module UpperDiagonalTarget = Endpoint Sides.G.square Sides.A.triangle j₀ Sides.upper-diagram-leg
      d₁ diagonal j₀-diagonal one vertex₂ (SquareCorner.vertex one one)
      d₁-one j₀-vertex₂ (Shapes.diagonal-vertex one) Shapes.UpperDiagonalTarget.comparison
    module UpperDiagonalTargetComparison = UpperDiagonalTarget.WithComparison Sides.UpperDiagonal.comparison Sides.UpperDiagonal.image
    module LeftSource = Endpoint Sides.G.square Sides.B.triangle j₁ Sides.lower-diagram-leg
      d₂ (insert zero) j₁-d₂ zero vertex₀ (SquareCorner.vertex zero zero)
      d₂-zero j₁-vertex₀ (SquareCorner.vertical-vertex zero zero) Shapes.LowerFirstSource.comparison
    module LeftSourceComparison = LeftSource.WithComparison Sides.Left.comparison Sides.Left.image
    module LeftTarget = Endpoint Sides.G.square Sides.B.triangle j₁ Sides.lower-diagram-leg
      d₂ (insert zero) j₁-d₂ one vertex₁ (SquareCorner.vertex one zero)
      d₂-one j₁-vertex₁ (SquareCorner.vertical-vertex one zero) Shapes.LowerFirstTarget.comparison
    module LeftTargetComparison = LeftTarget.WithComparison Sides.Left.comparison Sides.Left.image
    module BottomSource = Endpoint Sides.G.square Sides.B.triangle j₁ Sides.lower-diagram-leg
      d₀ (coinsert one) j₁-d₀ zero vertex₁ (SquareCorner.vertex one zero)
      d₀-zero j₁-vertex₁ (SquareCorner.horizontal-vertex one zero) Shapes.LowerSecondSource.comparison
    module BottomSourceComparison = BottomSource.WithComparison Sides.Bottom.comparison Sides.Bottom.image
    module BottomTarget = Endpoint Sides.G.square Sides.B.triangle j₁ Sides.lower-diagram-leg
      d₀ (coinsert one) j₁-d₀ one vertex₂ (SquareCorner.vertex one one)
      d₀-one j₁-vertex₂ (SquareCorner.horizontal-vertex one one) Shapes.LowerSecondTarget.comparison
    module BottomTargetComparison = BottomTarget.WithComparison Sides.Bottom.comparison Sides.Bottom.image
    module LowerDiagonalSource = Endpoint Sides.G.square Sides.B.triangle j₁ Sides.lower-diagram-leg
      d₁ diagonal j₁-diagonal zero vertex₀ (SquareCorner.vertex zero zero)
      d₁-zero j₁-vertex₀ (Shapes.diagonal-vertex zero) Shapes.LowerDiagonalSource.comparison
    module LowerDiagonalSourceComparison = LowerDiagonalSource.WithComparison Sides.lower-diagonal lower-image
    module LowerDiagonalTarget = Endpoint Sides.G.square Sides.B.triangle j₁ Sides.lower-diagram-leg
      d₁ diagonal j₁-diagonal one vertex₂ (SquareCorner.vertex one one)
      d₁-one j₁-vertex₂ (Shapes.diagonal-vertex one) Shapes.LowerDiagonalTarget.comparison
    module LowerDiagonalTargetComparison = LowerDiagonalTarget.WithComparison Sides.lower-diagonal lower-image

    module UpperMiddle = Corner ev₁ ev₀ (cone-restrict Sides.A.triangle (triangle-cone C))
      TopTarget.Source.frame RightSource.Source.frame TopTarget.Target.frame RightSource.Target.frame
      UpperJunction.compatibility Sides.Top.comparison Sides.Right.comparison TopTarget.vertex
      TopTargetComparison.compatible RightSourceComparison.compatible

    module LowerMiddle = Corner ev₁ ev₀ (cone-restrict Sides.B.triangle (triangle-cone C))
      LeftTarget.Source.frame BottomSource.Source.frame LeftTarget.Target.frame BottomSource.Target.frame
      LowerJunction.compatibility Sides.Left.comparison Sides.Bottom.comparison LeftTarget.vertex
      LeftTargetComparison.compatible BottomSourceComparison.compatible

    module UpperSource = Corner ev₀ ev₀ (cone-restrict Sides.A.triangle (Frames.source-cone))
      UpperDiagonalSource.Source.frame TopSource.Source.frame UpperDiagonalSource.Target.frame TopSource.Target.frame
      UpperSourceFrames.compatibility Sides.UpperDiagonal.comparison Sides.Top.comparison UpperDiagonalSource.vertex
      UpperDiagonalSourceComparison.compatible TopSourceComparison.compatible

    module LowerSource = Corner ev₀ ev₀ (cone-restrict Sides.B.triangle (Frames.source-cone))
      LowerDiagonalSource.Source.frame LeftSource.Source.frame LowerDiagonalSource.Target.frame LeftSource.Target.frame
      LowerSourceFrames.compatibility Sides.lower-diagonal Sides.Left.comparison LowerDiagonalSource.vertex
      LowerDiagonalSourceComparison.compatible LeftSourceComparison.compatible

    module UpperTarget = Corner ev₁ ev₁ (cone-restrict Sides.A.triangle (Frames.target-cone))
      UpperDiagonalTarget.Source.frame RightTarget.Source.frame UpperDiagonalTarget.Target.frame RightTarget.Target.frame
      UpperTargetFrames.compatibility Sides.UpperDiagonal.comparison Sides.Right.comparison UpperDiagonalTarget.vertex
      UpperDiagonalTargetComparison.compatible RightTargetComparison.compatible

    module LowerTarget = Corner ev₁ ev₁ (cone-restrict Sides.B.triangle (Frames.target-cone))
      LowerDiagonalTarget.Source.frame BottomTarget.Source.frame LowerDiagonalTarget.Target.frame BottomTarget.Target.frame
      LowerTargetFrames.compatibility Sides.lower-diagonal Sides.Bottom.comparison LowerDiagonalTarget.vertex
      LowerDiagonalTargetComparison.compatible BottomTargetComparison.compatible

module Complete {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C}
  {top : MorphismFamily x y} {right : MorphismFamily y z}
  {left : MorphismFamily x w} {bottom : MorphismFamily w z}
  {long : MorphismFamily x z}
  (given-upper : TrianglePresentation top right long)
  (given-lower : TrianglePresentation left bottom long) where
  module Construction = Six given-upper given-lower using (module Sides)
  module Diagonal = CommonDiagonal.At given-upper given-lower using (lower-image)
  module Transfers = Six.WithLowerDiagonalImage given-upper given-lower Diagonal.lower-image
  open Transfers public using
    (module UpperMiddle; module LowerMiddle; module UpperSource; module LowerSource;
      module UpperTarget; module LowerTarget)
```
