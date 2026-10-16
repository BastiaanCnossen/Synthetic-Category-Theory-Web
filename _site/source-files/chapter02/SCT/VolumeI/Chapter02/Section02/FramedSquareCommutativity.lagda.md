# The boundary composites of a framed square

Recover the actual square diagram from its vertical arrow. Its recurrying
comparison transports both vertical endpoint frames before the horizontal
endpoint equations are converted to complete native corner comparisons.
Both triangle restrictions will use one framed diagonal of that same square.

```agda
{-# OPTIONS --without-K --lossy-unification #-}
module SCT.VolumeI.Chapter02.Section02.FramedSquareCommutativity where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; comp-inv-left; comp-inv-right; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (cancel-left; cancel-right)
open import SCT.VolumeI.Chapter01.Section06.Cones
  using (Cone; ConeIdentification₁)
open import SCT.VolumeI.Chapter01.Section06.ConeFramings using (framed-cone)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Currying
  using (funCurry; funUncurry; funCurry-β; funCurry-η; curry⁼)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; evAt; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section02.SquareCoordinates using (module SquareCoordinates)
open import SCT.VolumeI.Chapter02.Section02.SquareCurrying using (module SquareCurrying)
import SCT.VolumeI.Chapter02.Section02.SquareCornerEndpoints as Endpoints

private
  module Recovery {Γ : Context} {P C : CAT Γ} (N : MAP P (Ar (Ar C))) where
    private
      I : CAT Γ
      I = [1]
      module Coordinate = SquareCoordinates P
      first : MAP (P × (I × I)) (P × I)
      first = pair pr₁ (pr₂ ∘ pr₂)
      last : MAP (P × (I × I)) I
      last = pr₁ ∘ pr₂
      backward : MAP (P × (I × I)) ((P × I) × I)
      backward = pair first last
      parameter : (pr₁ ∘ Coordinate.permute) =₁ (pr₁ ∘ pr₁)
      parameter = pair-β₁ Coordinate.parameter Coordinate.rectangle
      outer : ((pr₂ ∘ pr₂) ∘ Coordinate.permute) =₁ (pr₂ ∘ pr₁)
      outer = pair-β₂ Coordinate.inner Coordinate.outer ∙
        ((pr₂ ◁ pair-β₂ Coordinate.parameter Coordinate.rectangle) ∙
          comp-assoc Coordinate.permute pr₂ pr₂)
      inner : (last ∘ Coordinate.permute) =₁ pr₂
      inner = pair-β₁ Coordinate.inner Coordinate.outer ∙
        ((pr₁ ◁ pair-β₂ Coordinate.parameter Coordinate.rectangle) ∙
          comp-assoc Coordinate.permute pr₂ pr₁)
      backward-forward : (backward ∘ Coordinate.permute) =₁ id ((P × I) × I)
      backward-forward = pair-projections ∙
        (pair⁼ (pair-η pr₁) (id₌ pr₂) ∙
          (pair⁼ (pair⁼ parameter outer ∙ pair-pre pr₁ (pr₂ ∘ pr₂) Coordinate.permute) inner ∙
            pair-pre first last Coordinate.permute))
      diagram : MAP ((P × I) × I) C
      diagram = funUncurry (funUncurry N)
    square : MAP P (Fun (I × I) C)
    square = funCurry (diagram ∘ backward)
    module Curried = SquareCurrying square
    private
      raw : Curried.reordered =₁ diagram
      raw = comp-unitʳ diagram ∙
        ((diagram ◁ backward-forward) ∙
          (comp-assoc Coordinate.permute backward diagram ∙
            (funCurry-β (diagram ∘ backward) ▷ Coordinate.permute)))
      inner-comparison : Curried.first-curry =₁ funUncurry N
      inner-comparison = funCurry-η (funUncurry N) ∙
        curry⁼ (funEval {C = I} {D = C}) (funUniversal I C) raw
    comparison : Curried.nested =₁ N
    comparison = funCurry-η N ∙
      curry⁼ (funEval {C = I} {D = Ar C}) (funUniversal I (Ar C)) inner-comparison

  module NativeCornerFromEndpoint {Γ : Context} {P C : CAT Γ}
    (sigma : MAP P (Fun ([1] × [1]) C))
    (a b : MAP One ([1] {Γ = Γ})) (h k : MAP P (Ar C)) {z : MAP P C}
    (p : (evAt b ∘ h) =₁ z) (q : (evAt a ∘ k) =₁ z)
    (left : Endpoints.At.Curried.Horizontal.side sigma a =₁ h)
    (right : Endpoints.At.Curried.Vertical.side sigma b =₁ k) where
    module Native = Endpoints.At.NativeCorner sigma a b
    private
      module Normal = Endpoints.At.EndpointNormalization sigma a b h k p q left right
    horizontal-comparison : Native.Horizontal.evaluated =₁ h
    horizontal-comparison = left ∙ Native.Horizontal.comparison
    vertical-boundary : (evAt b ∘ Endpoints.At.Curried.nested sigma) =₁ k
    vertical-boundary = right ∙ Native.Vertical.boundary
    point-boundary : (evAt b ∘ Native.Horizontal.evaluated) =₁ (evAt a ∘ k)
    point-boundary = (evAt a ◁ vertical-boundary) ∙ Native.postcomposition-point
    private
      left-image = evAt b ◁ left
      right-image = evAt a ◁ right
      eta = Native.horizontal-endpoint
      boundary-image = evAt a ◁ Native.Vertical.boundary
      point = Native.postcomposition-point
      K = Native.matching
      left-normal : (p ∙ (evAt b ◁ horizontal-comparison)) =₂ ((p ∙ left-image) ∙ eta)
      left-normal = Normal.left-normal
      right-normal : ((q ∙ (right-image ∙ K)) ∙ eta) =₂ (q ∙ point-boundary)
      right-normal = Normal.right-normal
    module From
      (endpoint : (p ∙ (evAt b ◁ horizontal-comparison)) =₂ (q ∙ point-boundary)) where
      private
        corner : (p ∙ left-image) =₂ (q ∙ (right-image ∙ K))
        corner = cancel-right eta ((right-normal ⁻¹) ∙ (endpoint ∙ (left-normal ⁻¹)))
        compatible : ((q ⁻¹ ∙ p) ∙ left-image) =₂ (right-image ∙ K)
        compatible = cancel-left q
          (corner ∙ (comp₌-cong (comp-inv-left q p) (id₌ left-image) ∙
            (comp₌-assoc q (q ⁻¹ ∙ p) left-image) ⁻¹))
      value : ConeIdentification₁ Native.cone (framed-cone (evAt b) (evAt a) h k p q)
      value = record { left = left; right = right; compatible = compatible }


  corner-from-endpoint : {Γ : Context} {P C : CAT Γ}
    (sigma : MAP P (Fun ([1] × [1]) C))
    (a b : MAP One ([1] {Γ = Γ})) (h k : MAP P (Ar C)) {z : MAP P C}
    (p : (evAt b ∘ h) =₁ z) (q : (evAt a ∘ k) =₁ z)
    (left : Endpoints.At.Curried.Horizontal.side sigma a =₁ h)
    (right : Endpoints.At.Curried.Vertical.side sigma b =₁ k)
    → (p ∙ (evAt b ◁ NativeCornerFromEndpoint.horizontal-comparison sigma a b h k p q left right))
        =₂ (q ∙ NativeCornerFromEndpoint.point-boundary sigma a b h k p q left right)
    → ConeIdentification₁ (Endpoints.At.NativeCorner.cone sigma a b)
        (framed-cone (evAt b) (evAt a) h k p q)
  corner-from-endpoint {Γ = Γ} {P = P} {C = C} sigma a b h k p q left right endpoint =
    NativeCornerFromEndpoint.From.value {Γ = Γ} {P = P} {C = C}
      sigma a b h k p q left right endpoint
```


The two actual triangle restrictions share the diagonal restriction itself.
Each reflected face comparison has its own computation in the square diagram;
no inverse gluing or replacement of its matching is involved.

```agda
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction using (product-restriction; restriction-compositor)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section06.Cones using (cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (cone-inverse)
open import SCT.VolumeI.Chapter01.Section06.FramedConeTransport using (module Corner)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-uncurry)
open import SCT.VolumeI.Chapter01.Section07.Currying using (reflect; reflect-β-One)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt-cong; evAt-pre)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using ([2]; d₀; d₁; d₂; vertex₀; vertex₁; vertex₂;
    d₂-zero; d₂-one; d₀-zero; d₀-one; d₁-zero; d₁-one)
open import SCT.VolumeI.Chapter02.Section01.SquareGluing
  using (j₀; j₁; diagonal; j₀-d₂; j₀-d₀; j₁-d₂; j₁-d₀; j₀-diagonal; j₁-diagonal;
    j₀-vertex₀; j₀-vertex₁; j₀-vertex₂; j₁-vertex₀; j₁-vertex₁; j₁-vertex₂)
open import SCT.VolumeI.Chapter02.Section02.SquareCoordinates using (coinsert)
open import SCT.VolumeI.Chapter02.Section02.SquareCorners using (module SquareCorner)
open import SCT.VolumeI.Chapter02.Section02.SquareVertexShapes using (module At)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module CornerRestriction; module TriangleCornerFrames)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (triangle-cone; triangle-junction-vertex)
open import SCT.VolumeI.Chapter02.Section02.SquareBoundaryCones using (module Endpoint)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations using (TrianglePresentation; triangle-presentation)

private
  module Geometry {Γ : Context} {P C : CAT Γ} (sigma : MAP P (Fun ([1] × [1]) C)) where
    upper : MAP P (Fun [2] C)
    upper = funPre j₀ ∘ sigma
    lower : MAP P (Fun [2] C)
    lower = funPre j₁ ∘ sigma
    upper-leg : (funUncurry sigma ∘ product-restriction {P = P} j₀) =₁ funUncurry upper
    upper-leg = (funPre-uncurry j₀ sigma) ⁻¹
    lower-leg : (funUncurry sigma ∘ product-restriction {P = P} j₁) =₁ funUncurry lower
    lower-leg = (funPre-uncurry j₁ sigma) ⁻¹
    module Face (j : MAP [2] ([1] × [1]))
      (triangle : MAP P (Fun [2] C))
      (leg : (funUncurry sigma ∘ product-restriction {P = P} j) =₁ funUncurry triangle)
      (d : MAP [1] [2]) (r : MAP [1] ([1] × [1]))
      (shape : (j ∘ d) =₁ r) where
      source : MAP P (Ar C)
      source = funPre {D = C} r ∘ sigma
      target : MAP P (Ar C)
      target = funPre {D = C} d ∘ triangle
      source-beta : funUncurry source =₁ (funUncurry sigma ∘ product-restriction {P = P} r)
      source-beta = funPre-uncurry r sigma
      target-beta : funUncurry target =₁ (funUncurry triangle ∘ product-restriction {P = P} d)
      target-beta = funPre-uncurry d triangle
      axis : (product-restriction {P = P} j ∘ product-restriction d) =₁ product-restriction r
      axis = productMap-cong (id₌ (id P)) shape ∙ restriction-compositor d j
      axis-route : ((funUncurry sigma ∘ product-restriction {P = P} j) ∘ product-restriction d)
        =₁ (funUncurry sigma ∘ product-restriction r)
      axis-route = post-triangle (funUncurry sigma) (product-restriction {P = P} j)
        (product-restriction d) axis
  
      diagram-comparison : funUncurry source =₁ funUncurry target
      diagram-comparison = target-beta ⁻¹ ∙
        ((leg ▷ product-restriction {P = P} d) ∙ (axis-route ⁻¹ ∙ source-beta))
  
      comparison : source =₁ target
      comparison = reflect (funEval {C = [1]} {D = C}) (funUniversal [1] C)
        source target diagram-comparison
  
      image : evaluate-cong (funEval {C = [1]} {D = C}) comparison =₂ diagram-comparison
      image = reflect-β-One (funEval {C = [1]} {D = C}) (funUniversal [1] C)
        source target diagram-comparison
  
    module Top = Face j₀ upper upper-leg d₂ (coinsert zero) j₀-d₂
    module Right = Face j₀ upper upper-leg d₀ (insert one) j₀-d₀
    module Left = Face j₁ lower lower-leg d₂ (insert zero) j₁-d₂
    module Bottom = Face j₁ lower lower-leg d₀ (coinsert one) j₁-d₀
    module UpperDiagonal = Face j₀ upper upper-leg d₁ diagonal j₀-diagonal
  
    module LowerDiagonal = Face j₁ lower lower-leg d₁ diagonal j₁-diagonal
  
    module Shapes = At {Γ = Γ}
    module Frames = TriangleCornerFrames C
    module UpperJunction = CornerRestriction ev₁ ev₀ (triangle-cone C)
      (evAt-cong d₂-one ∙ evAt-pre one d₂)
      (evAt-cong d₀-zero ∙ evAt-pre zero d₀) (triangle-junction-vertex C) upper
    module LowerJunction = CornerRestriction ev₁ ev₀ (triangle-cone C)
      (evAt-cong d₂-one ∙ evAt-pre one d₂)
      (evAt-cong d₀-zero ∙ evAt-pre zero d₀) (triangle-junction-vertex C) lower
    module UpperSourceFrames = Frames.Source upper
    module LowerSourceFrames = Frames.Source lower
    module UpperTargetFrames = Frames.Target upper
    module LowerTargetFrames = Frames.Target lower
  
    module TopSource = Endpoint sigma upper j₀ upper-leg
      d₂ (coinsert zero) j₀-d₂ zero vertex₀ (SquareCorner.vertex zero zero)
      d₂-zero j₀-vertex₀ (SquareCorner.horizontal-vertex zero zero) Shapes.UpperFirstSource.comparison
    module TopSourceComparison = TopSource.WithComparison Top.comparison Top.image
    module TopTarget = Endpoint sigma upper j₀ upper-leg
      d₂ (coinsert zero) j₀-d₂ one vertex₁ (SquareCorner.vertex zero one)
      d₂-one j₀-vertex₁ (SquareCorner.horizontal-vertex zero one) Shapes.UpperFirstTarget.comparison
    module TopTargetComparison = TopTarget.WithComparison Top.comparison Top.image
    module RightSource = Endpoint sigma upper j₀ upper-leg
      d₀ (insert one) j₀-d₀ zero vertex₁ (SquareCorner.vertex zero one)
      d₀-zero j₀-vertex₁ (SquareCorner.vertical-vertex zero one) Shapes.UpperSecondSource.comparison
    module RightSourceComparison = RightSource.WithComparison Right.comparison Right.image
    module RightTarget = Endpoint sigma upper j₀ upper-leg
      d₀ (insert one) j₀-d₀ one vertex₂ (SquareCorner.vertex one one)
      d₀-one j₀-vertex₂ (SquareCorner.vertical-vertex one one) Shapes.UpperSecondTarget.comparison
    module RightTargetComparison = RightTarget.WithComparison Right.comparison Right.image
    module UpperDiagonalSource = Endpoint sigma upper j₀ upper-leg
      d₁ diagonal j₀-diagonal zero vertex₀ (SquareCorner.vertex zero zero)
      d₁-zero j₀-vertex₀ (Shapes.diagonal-vertex zero) Shapes.UpperDiagonalSource.comparison
    module UpperDiagonalSourceComparison = UpperDiagonalSource.WithComparison UpperDiagonal.comparison UpperDiagonal.image
    module UpperDiagonalTarget = Endpoint sigma upper j₀ upper-leg
      d₁ diagonal j₀-diagonal one vertex₂ (SquareCorner.vertex one one)
      d₁-one j₀-vertex₂ (Shapes.diagonal-vertex one) Shapes.UpperDiagonalTarget.comparison
    module UpperDiagonalTargetComparison = UpperDiagonalTarget.WithComparison UpperDiagonal.comparison UpperDiagonal.image
    module LeftSource = Endpoint sigma lower j₁ lower-leg
      d₂ (insert zero) j₁-d₂ zero vertex₀ (SquareCorner.vertex zero zero)
      d₂-zero j₁-vertex₀ (SquareCorner.vertical-vertex zero zero) Shapes.LowerFirstSource.comparison
    module LeftSourceComparison = LeftSource.WithComparison Left.comparison Left.image
    module LeftTarget = Endpoint sigma lower j₁ lower-leg
      d₂ (insert zero) j₁-d₂ one vertex₁ (SquareCorner.vertex one zero)
      d₂-one j₁-vertex₁ (SquareCorner.vertical-vertex one zero) Shapes.LowerFirstTarget.comparison
    module LeftTargetComparison = LeftTarget.WithComparison Left.comparison Left.image
    module BottomSource = Endpoint sigma lower j₁ lower-leg
      d₀ (coinsert one) j₁-d₀ zero vertex₁ (SquareCorner.vertex one zero)
      d₀-zero j₁-vertex₁ (SquareCorner.horizontal-vertex one zero) Shapes.LowerSecondSource.comparison
    module BottomSourceComparison = BottomSource.WithComparison Bottom.comparison Bottom.image
    module BottomTarget = Endpoint sigma lower j₁ lower-leg
      d₀ (coinsert one) j₁-d₀ one vertex₂ (SquareCorner.vertex one one)
      d₀-one j₁-vertex₂ (SquareCorner.horizontal-vertex one one) Shapes.LowerSecondTarget.comparison
    module BottomTargetComparison = BottomTarget.WithComparison Bottom.comparison Bottom.image
    module LowerDiagonalSource = Endpoint sigma lower j₁ lower-leg
      d₁ diagonal j₁-diagonal zero vertex₀ (SquareCorner.vertex zero zero)
      d₁-zero j₁-vertex₀ (Shapes.diagonal-vertex zero) Shapes.LowerDiagonalSource.comparison
    module LowerDiagonalSourceComparison = LowerDiagonalSource.WithComparison LowerDiagonal.comparison LowerDiagonal.image
    module LowerDiagonalTarget = Endpoint sigma lower j₁ lower-leg
      d₁ diagonal j₁-diagonal one vertex₂ (SquareCorner.vertex one one)
      d₁-one j₁-vertex₂ (Shapes.diagonal-vertex one) Shapes.LowerDiagonalTarget.comparison
    module LowerDiagonalTargetComparison = LowerDiagonalTarget.WithComparison LowerDiagonal.comparison LowerDiagonal.image

    module UpperMiddle = Corner ev₁ ev₀ (cone-restrict upper (triangle-cone C))
      TopTarget.Source.frame RightSource.Source.frame TopTarget.Target.frame RightSource.Target.frame
      UpperJunction.compatibility Top.comparison Right.comparison TopTarget.vertex
      TopTargetComparison.compatible RightSourceComparison.compatible

    module LowerMiddle = Corner ev₁ ev₀ (cone-restrict lower (triangle-cone C))
      LeftTarget.Source.frame BottomSource.Source.frame LeftTarget.Target.frame BottomSource.Target.frame
      LowerJunction.compatibility Left.comparison Bottom.comparison LeftTarget.vertex
      LeftTargetComparison.compatible BottomSourceComparison.compatible

    module UpperSource = Corner ev₀ ev₀ (cone-restrict upper (Frames.source-cone))
      UpperDiagonalSource.Source.frame TopSource.Source.frame UpperDiagonalSource.Target.frame TopSource.Target.frame
      UpperSourceFrames.compatibility UpperDiagonal.comparison Top.comparison UpperDiagonalSource.vertex
      UpperDiagonalSourceComparison.compatible TopSourceComparison.compatible

    module LowerSource = Corner ev₀ ev₀ (cone-restrict lower (Frames.source-cone))
      LowerDiagonalSource.Source.frame LeftSource.Source.frame LowerDiagonalSource.Target.frame LeftSource.Target.frame
      LowerSourceFrames.compatibility LowerDiagonal.comparison Left.comparison LowerDiagonalSource.vertex
      LowerDiagonalSourceComparison.compatible LeftSourceComparison.compatible

    module UpperTarget = Corner ev₁ ev₁ (cone-restrict upper (Frames.target-cone))
      UpperDiagonalTarget.Source.frame RightTarget.Source.frame UpperDiagonalTarget.Target.frame RightTarget.Target.frame
      UpperTargetFrames.compatibility UpperDiagonal.comparison Right.comparison UpperDiagonalTarget.vertex
      UpperDiagonalTargetComparison.compatible RightTargetComparison.compatible

    module LowerTarget = Corner ev₁ ev₁ (cone-restrict lower (Frames.target-cone))
      LowerDiagonalTarget.Source.frame BottomTarget.Source.frame LowerDiagonalTarget.Target.frame BottomTarget.Target.frame
      LowerTargetFrames.compatibility LowerDiagonal.comparison Bottom.comparison LowerDiagonalTarget.vertex
      LowerDiagonalTargetComparison.compatible BottomTargetComparison.compatible


    x y w z : MAP P C
    x = evAt (SquareCorner.vertex zero zero) ∘ sigma
    y = evAt (SquareCorner.vertex zero one) ∘ sigma
    w = evAt (SquareCorner.vertex one zero) ∘ sigma
    z = evAt (SquareCorner.vertex one one) ∘ sigma
    top : MorphismFamily x y
    top = record { arrow = Top.source; source-frame = TopSource.Source.frame; target-frame = TopTarget.Source.frame }
    right : MorphismFamily y z
    right = record { arrow = Right.source; source-frame = RightSource.Source.frame; target-frame = RightTarget.Source.frame }
    left : MorphismFamily x w
    left = record { arrow = Left.source; source-frame = LeftSource.Source.frame; target-frame = LeftTarget.Source.frame }
    bottom : MorphismFamily w z
    bottom = record { arrow = Bottom.source; source-frame = BottomSource.Source.frame; target-frame = BottomTarget.Source.frame }
    long : MorphismFamily x z
    long = record { arrow = UpperDiagonal.source; source-frame = UpperDiagonalSource.Source.frame; target-frame = UpperDiagonalTarget.Source.frame }

    upper-presentation : TrianglePresentation top right long
    upper-presentation = triangle-presentation upper
      (Top.comparison ⁻¹) (Right.comparison ⁻¹) (UpperDiagonal.comparison ⁻¹)
      (ConeIdentification₁.compatible (cone-inverse UpperMiddle.comparison))
      (ConeIdentification₁.compatible (cone-inverse UpperSource.comparison))
      (ConeIdentification₁.compatible (cone-inverse UpperTarget.comparison))
    lower-presentation : TrianglePresentation left bottom long
    lower-presentation = triangle-presentation lower
      (Left.comparison ⁻¹) (Bottom.comparison ⁻¹) (LowerDiagonal.comparison ⁻¹)
      (ConeIdentification₁.compatible (cone-inverse LowerMiddle.comparison))
      (ConeIdentification₁.compatible (cone-inverse LowerSource.comparison))
      (ConeIdentification₁.compatible (cone-inverse LowerTarget.comparison))
```

The native corner comparison supplies the change of its vertex. Its other
leg then has that same vertex image by the complete matching equation.
This transfers the two whole presentations to the original four families.

```agda
open import SCT.VolumeI.Chapter01.Section02.Specialization using (inv-comp-left; inv-comp-right)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations
  using (family-comparison; retarget-family; retarget-family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons
  using (compose-family-comparisons; inverse-family-comparison; id-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyPostcomposition using (post-family-comparison)
open import SCT.VolumeI.Chapter02.Section02.FramedSquares using (FramedSquare; framed-image; module SquareFamily)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (module RetargetPresentation; presented-composition)
open import SCT.VolumeI.Chapter02.Section02.TrianglePresentationChange using (module ReplacePresentation)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

private
  module NativeVertexChange {Γ : Context} {P A B C : CAT Γ}
    (f : MAP A C) (g : MAP B C) (native : Cone f g P)
    {v z : MAP P C} {h : MAP P A} {k : MAP P B}
    (p₀ : (f ∘ Cone.left native) =₁ v) (q₀ : (g ∘ Cone.right native) =₁ v)
    (junction : (q₀ ∙ Cone.match native) =₂ p₀)
    (p : (f ∘ h) =₁ z) (q : (g ∘ k) =₁ z)
    (given : ConeIdentification₁ native (framed-cone f g h k p q)) where
    left = ConeIdentification₁.left given
    right = ConeIdentification₁.right given
    private
      L = f ◁ left
      R = g ◁ right
      K = Cone.match native
    vertex : v =₁ z
    vertex = q ∙ (R ∙ q₀ ⁻¹)
    right-endpoint : (q ∙ R) =₂ (vertex ∙ q₀)
    right-endpoint =
      (comp₌-cong (id₌ q) (inv-comp-right R q₀) ∙
        comp₌-assoc q (R ∙ q₀ ⁻¹) q₀) ⁻¹
    private
      quotient : (q₀ ⁻¹ ∙ p₀) =₂ K
      quotient = inv-comp-left q₀ K ∙ comp₌-cong (id₌ (q₀ ⁻¹)) (junction ⁻¹)
      corner : (p ∙ L) =₂ (q ∙ (R ∙ K))
      corner = comp₌-cong (id₌ q) (ConeIdentification₁.compatible given) ∙
        (comp₌-assoc q (q ⁻¹ ∙ p) L ∙
          (comp₌-cong (comp-inv-left q p) (id₌ L)) ⁻¹)
      vertex-normal : (vertex ∙ p₀) =₂ (q ∙ (R ∙ K))
      vertex-normal = comp₌-cong (id₌ q) (comp₌-cong (id₌ R) quotient) ∙
        (comp₌-cong (id₌ q) (comp₌-assoc R (q₀ ⁻¹) p₀) ∙
          comp₌-assoc q (R ∙ q₀ ⁻¹) p₀)
    left-endpoint : (p ∙ L) =₂ (vertex ∙ p₀)
    left-endpoint = vertex-normal ⁻¹ ∙ corner

  module RecoverBoundary {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C}
    {top : MorphismFamily x y} {right : MorphismFamily y z}
    {left : MorphismFamily x w} {bottom : MorphismFamily w z}
    (given : FramedSquare top right left bottom) where
    module S = SquareFamily given
    module N = MorphismFamily S.vertical
    module T = MorphismFamily top
    module R = MorphismFamily right
    module L = MorphismFamily left
    module B = MorphismFamily bottom
    module Recover = Recovery {Γ = Γ} {P = P} {C = C} N.arrow
    module Curried = Recover.Curried
    square : MAP P (Fun ([1] × [1]) C)
    square = Recover.square
    epsilon : Curried.nested =₁ N.arrow
    epsilon = Recover.comparison
    left-frame : (ev₀ {C = Ar C} ∘ Curried.nested) =₁ L.arrow
    left-frame = N.source-frame ∙ (ev₀ ◁ epsilon)
    right-frame : (ev₁ {C = Ar C} ∘ Curried.nested) =₁ R.arrow
    right-frame = N.target-frame ∙ (ev₁ ◁ epsilon)
    left-side : Curried.Vertical.side zero =₁ L.arrow
    left-side = left-frame ∙ (Curried.Vertical.boundary zero) ⁻¹
    right-side : Curried.Vertical.side one =₁ R.arrow
    right-side = right-frame ∙ (Curried.Vertical.boundary one) ⁻¹
    recovered-vertical : MorphismFamily L.arrow R.arrow
    recovered-vertical = record
      { arrow = Curried.nested
      ; source-frame = left-side ∙ Curried.Vertical.boundary zero
      ; target-frame = right-side ∙ Curried.Vertical.boundary one }
    vertical-comparison : MorphismFamilyIdentification One recovered-vertical S.vertical
    vertical-comparison = family-comparison recovered-vertical S.vertical epsilon
      ((inv-comp-right left-frame (Curried.Vertical.boundary zero)) ⁻¹)
      ((inv-comp-right right-frame (Curried.Vertical.boundary one)) ⁻¹)
    top-edge : MorphismFamilyIdentification One
      (framed-image (ev₀ {C = C}) recovered-vertical L.source-frame R.source-frame) top
    top-edge = compose-family-comparisons S.top-edge
      (retarget-family-comparison L.source-frame R.source-frame
        (post-family-comparison (ev₀ {C = C}) vertical-comparison))
    bottom-edge : MorphismFamilyIdentification One
      (framed-image (ev₁ {C = C}) recovered-vertical L.target-frame R.target-frame) bottom
    bottom-edge = compose-family-comparisons S.bottom-edge
      (retarget-family-comparison L.target-frame R.target-frame
        (post-family-comparison (ev₁ {C = C}) vertical-comparison))
    module Top = FamilyComparison top-edge
    module Bottom = FamilyComparison bottom-edge
    top-side : Curried.Horizontal.side zero =₁ T.arrow
    top-side = Top.identification ∙ (Curried.Horizontal.comparison zero) ⁻¹
    bottom-side : Curried.Horizontal.side one =₁ B.arrow
    bottom-side = Bottom.identification ∙ (Curried.Horizontal.comparison one) ⁻¹
    top-image : (top-side ∙ Curried.Horizontal.comparison zero) =₂ Top.identification
    top-image = inv-comp-right Top.identification (Curried.Horizontal.comparison zero)
    bottom-image : (bottom-side ∙ Curried.Horizontal.comparison one) =₂ Bottom.identification
    bottom-image = inv-comp-right Bottom.identification (Curried.Horizontal.comparison one)
    native₀₀ : ConeIdentification₁ (Endpoints.At.NativeCorner.cone square zero zero)
      (framed-cone ev₀ ev₀ T.arrow L.arrow T.source-frame L.source-frame)
    native₀₀ = corner-from-endpoint {Γ = Γ} {P = P} {C = C} square zero zero T.arrow L.arrow
      T.source-frame L.source-frame top-side left-side
      (Top.source ∙ comp₌-cong (id₌ T.source-frame) (postWhisker ev₀ ◁ top-image))
    native₀₁ : ConeIdentification₁ (Endpoints.At.NativeCorner.cone square zero one)
      (framed-cone ev₁ ev₀ T.arrow R.arrow T.target-frame R.source-frame)
    native₀₁ = corner-from-endpoint {Γ = Γ} {P = P} {C = C} square zero one T.arrow R.arrow
      T.target-frame R.source-frame top-side right-side
      (Top.target ∙ comp₌-cong (id₌ T.target-frame) (postWhisker ev₁ ◁ top-image))
    native₁₀ : ConeIdentification₁ (Endpoints.At.NativeCorner.cone square one zero)
      (framed-cone ev₀ ev₁ B.arrow L.arrow B.source-frame L.target-frame)
    native₁₀ = corner-from-endpoint {Γ = Γ} {P = P} {C = C} square one zero B.arrow L.arrow
      B.source-frame L.target-frame bottom-side left-side
      (Bottom.source ∙ comp₌-cong (id₌ B.source-frame) (postWhisker ev₀ ◁ bottom-image))
    native₁₁ : ConeIdentification₁ (Endpoints.At.NativeCorner.cone square one one)
      (framed-cone ev₁ ev₁ B.arrow R.arrow B.target-frame R.target-frame)
    native₁₁ = corner-from-endpoint {Γ = Γ} {P = P} {C = C} square one one B.arrow R.arrow
      B.target-frame R.target-frame bottom-side right-side
      (Bottom.target ∙ comp₌-cong (id₌ B.target-frame) (postWhisker ev₁ ◁ bottom-image))
```

```agda
private
  module BoundaryPresentations {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C}
    {top : MorphismFamily x y} {right : MorphismFamily y z}
    {left : MorphismFamily x w} {bottom : MorphismFamily w z}
    (given : FramedSquare top right left bottom) where
    module Recovered = RecoverBoundary given
    module G = Geometry Recovered.square
      using (x; y; w; z; top; right; left; bottom; long; upper-presentation; lower-presentation)
    module T = MorphismFamily top
    module R = MorphismFamily right
    module L = MorphismFamily left
    module B = MorphismFamily bottom
    module NativeFrames (a b : MAP One ([1] {Γ = Γ})) where
      module Shape = SquareCorner a b
      module E = Shape.Evaluated C
      module Frames = CornerRestriction (evAt b) (evAt a) E.cone
        E.horizontal E.vertical E.vertex-equation Recovered.square
    module Frames₀₀ = NativeFrames zero zero
    module Frames₀₁ = NativeFrames zero one
    module Frames₁₀ = NativeFrames one zero
    module Frames₁₁ = NativeFrames one one
    module Vertex₀₀ = NativeVertexChange ev₀ ev₀ (Endpoints.At.NativeCorner.cone Recovered.square zero zero)
      Frames₀₀.Frames.left-frame Frames₀₀.Frames.right-frame Frames₀₀.Frames.compatibility
      T.source-frame L.source-frame Recovered.native₀₀
    module Vertex₀₁ = NativeVertexChange ev₁ ev₀ (Endpoints.At.NativeCorner.cone Recovered.square zero one)
      Frames₀₁.Frames.left-frame Frames₀₁.Frames.right-frame Frames₀₁.Frames.compatibility
      T.target-frame R.source-frame Recovered.native₀₁
    module Vertex₁₀ = NativeVertexChange ev₀ ev₁ (Endpoints.At.NativeCorner.cone Recovered.square one zero)
      Frames₁₀.Frames.left-frame Frames₁₀.Frames.right-frame Frames₁₀.Frames.compatibility
      B.source-frame L.target-frame Recovered.native₁₀
    module Vertex₁₁ = NativeVertexChange ev₁ ev₁ (Endpoints.At.NativeCorner.cone Recovered.square one one)
      Frames₁₁.Frames.left-frame Frames₁₁.Frames.right-frame Frames₁₁.Frames.compatibility
      B.target-frame R.target-frame Recovered.native₁₁
    x-change : G.x =₁ x
    x-change = Vertex₀₀.vertex
    y-change : G.y =₁ y
    y-change = Vertex₀₁.vertex
    w-change : G.w =₁ w
    w-change = Vertex₁₀.vertex
    z-change : G.z =₁ z
    z-change = Vertex₁₁.vertex
    top-comparison : MorphismFamilyIdentification One (retarget-family G.top x-change y-change) top
    top-comparison = family-comparison _ top Recovered.top-side
      Vertex₀₀.left-endpoint Vertex₀₁.left-endpoint
    right-comparison : MorphismFamilyIdentification One (retarget-family G.right y-change z-change) right
    right-comparison = family-comparison _ right Recovered.right-side
      Vertex₀₁.right-endpoint Vertex₁₁.right-endpoint
    left-comparison : MorphismFamilyIdentification One (retarget-family G.left x-change w-change) left
    left-comparison = family-comparison _ left Recovered.left-side
      Vertex₀₀.right-endpoint Vertex₁₀.right-endpoint
    bottom-comparison : MorphismFamilyIdentification One (retarget-family G.bottom w-change z-change) bottom
    bottom-comparison = family-comparison _ bottom Recovered.bottom-side
      Vertex₁₀.left-endpoint Vertex₁₁.left-endpoint
    long : MorphismFamily x z
    long = retarget-family G.long x-change z-change
    upper : TrianglePresentation top right long
    upper = ReplacePresentation.value
      (RetargetPresentation.value G.upper-presentation x-change y-change z-change)
      top-comparison right-comparison (id-family-comparison long)
    lower : TrianglePresentation left bottom long
    lower = ReplacePresentation.value
      (RetargetPresentation.value G.lower-presentation x-change w-change z-change)
      left-comparison bottom-comparison (id-family-comparison long)

module _ {Γ : Context} where
  comparison : (C : CAT Γ) (segal : IsEquiv (short-edges C))
    {P : CAT Γ} {x y z w : MAP P C}
    {top : MorphismFamily x y} {right : MorphismFamily y z}
    {left : MorphismFamily x w} {bottom : MorphismFamily w z}
    → FramedSquare top right left bottom
    → MorphismFamilyIdentification One
        (MC.Composition.compose C segal bottom left)
        (MC.Composition.compose C segal right top)
  comparison C segal {top = top} {right} {left} {bottom} given =
    compose-family-comparisons
      (inverse-family-comparison (presented-composition segal top right Presentations.long Presentations.upper))
      (presented-composition segal left bottom Presentations.long Presentations.lower)
    where module Presentations = BoundaryPresentations given using (long; upper; lower)
```
