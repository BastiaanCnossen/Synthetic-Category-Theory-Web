# A prescribed framed square from two complete triangle presentations

The six full geometric transfers are pasted with the original triangle
presentations. The outer corners pass through their jointly chosen diagonal.
The native square matchings are restored explicitly before endpoint
conversion, retaining the selected side legs and all four endpoint frames.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.GluedFramedSquares where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section06.Cones using (ConeIdentification₁)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (cone-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeFramings using (framed-cone)
open import SCT.VolumeI.Chapter01.Section06.FramedConePasting
  using (unframe-source; swap-framed; module ThroughCommon)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (ev₀; ev₁; evAt; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations using (TrianglePresentation)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module CornerRestriction)
open import SCT.VolumeI.Chapter02.Section02.SquareCorners using (module SquareCorner)
open import SCT.VolumeI.Chapter02.Section02.SquareBoundaryCones using (module Complete)
open import SCT.VolumeI.Chapter02.Section02.SquareCornerEndpoints using (module At)
open import SCT.VolumeI.Chapter02.Section02.WholeCornerFramedSquares using (module AtSquare)
open import SCT.VolumeI.Chapter02.Section02.FramedSquares using (FramedSquare)

module Glue {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C}
  {top : MorphismFamily x y} {right : MorphismFamily y z}
  {left : MorphismFamily x w} {bottom : MorphismFamily w z}
  {long : MorphismFamily x z}
  (given-upper : TrianglePresentation top right long)
  (given-lower : TrianglePresentation left bottom long) where
  module Boundary = Complete given-upper given-lower
  module Transfer = Boundary.Transfers
  module Sides = Boundary.Construction.Sides
  module A = Sides.A
  module B = Sides.B
  module Endpoint = At Sides.G.square
  module Assembly = AtSquare Sides.G.square top right left bottom
  private
    module T = MorphismFamily top
    module R = MorphismFamily right
    module L = MorphismFamily left
    module Bottom = MorphismFamily bottom
    module D = MorphismFamily long

    module NativeFrames (a b : MAP One ([1] {Γ = Γ})) where
      module Shape = SquareCorner a b
      module Evaluated = Shape.Evaluated C
      module Frames = CornerRestriction (evAt b) (evAt a) Evaluated.cone
        Evaluated.horizontal Evaluated.vertical Evaluated.vertex-equation Sides.G.square

  upper-middle = cone-compose A.short-comparison Transfer.UpperMiddle.comparison
  lower-middle = cone-compose B.short-comparison Transfer.LowerMiddle.comparison
  upper-source = cone-compose A.source-comparison Transfer.UpperSource.comparison
  lower-source = cone-compose B.source-comparison Transfer.LowerSource.comparison
  upper-target = cone-compose A.target-comparison Transfer.UpperTarget.comparison
  lower-target = cone-compose B.target-comparison Transfer.LowerTarget.comparison

  common-diagonal : ConeIdentification₁.left lower-source =₂ ConeIdentification₁.left upper-source
  common-diagonal = Sides.diagonal-compatible

  module Source = ThroughCommon
    Transfer.UpperDiagonalSource.Source.frame Transfer.TopSource.Source.frame Transfer.LeftSource.Source.frame
    D.source-frame T.source-frame L.source-frame upper-source lower-source common-diagonal
  module Target = ThroughCommon
    Transfer.LowerDiagonalTarget.Source.frame Transfer.BottomTarget.Source.frame Transfer.RightTarget.Source.frame
    D.target-frame Bottom.target-frame R.target-frame lower-target upper-target (common-diagonal ⁻¹)

  private
    module Native₀₀ = NativeFrames zero zero
    module Native₀₁ = NativeFrames zero one
    module Native₁₀ = NativeFrames one zero
    module Native₁₁ = NativeFrames one one

    lower-middle-swapped = swap-framed
      Transfer.LeftTarget.Source.frame Transfer.BottomSource.Source.frame
      L.target-frame Bottom.source-frame lower-middle

  corner₀₀ : ConeIdentification₁ (Endpoint.NativeCorner.cone zero zero)
    (framed-cone ev₀ ev₀ T.arrow L.arrow T.source-frame L.source-frame)
  corner₀₀ = unframe-source Transfer.TopSource.Source.frame Transfer.LeftSource.Source.frame
    (Endpoint.NativeCorner.matching zero zero) Native₀₀.Frames.compatibility Source.comparison

  corner₀₁ : ConeIdentification₁ (Endpoint.NativeCorner.cone zero one)
    (framed-cone ev₁ ev₀ T.arrow R.arrow T.target-frame R.source-frame)
  corner₀₁ = unframe-source Transfer.TopTarget.Source.frame Transfer.RightSource.Source.frame
    (Endpoint.NativeCorner.matching zero one) Native₀₁.Frames.compatibility upper-middle

  corner₁₀ : ConeIdentification₁ (Endpoint.NativeCorner.cone one zero)
    (framed-cone ev₀ ev₁ Bottom.arrow L.arrow Bottom.source-frame L.target-frame)
  corner₁₀ = unframe-source Transfer.BottomSource.Source.frame Transfer.LeftTarget.Source.frame
    (Endpoint.NativeCorner.matching one zero) Native₁₀.Frames.compatibility lower-middle-swapped

  corner₁₁ : ConeIdentification₁ (Endpoint.NativeCorner.cone one one)
    (framed-cone ev₁ ev₁ Bottom.arrow R.arrow Bottom.target-frame R.target-frame)
  corner₁₁ = unframe-source Transfer.BottomTarget.Source.frame Transfer.RightTarget.Source.frame
    (Endpoint.NativeCorner.matching one one) Native₁₁.Frames.compatibility Target.comparison

  module Assembled = Assembly.Assemble corner₀₀ corner₀₁ corner₁₀ corner₁₁
    (id₌ (A.first ∙ Sides.Top.comparison))
    (id₌ (B.first ∙ Sides.Left.comparison))
    (id₌ (B.second ∙ Sides.Bottom.comparison))
    (id₌ (A.second ∙ Sides.Right.comparison))

  value : FramedSquare top right left bottom
  value = Assembled.value
```
