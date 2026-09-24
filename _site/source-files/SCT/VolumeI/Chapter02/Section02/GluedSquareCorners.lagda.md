# The four retained corners of a glued square

The two middle corners are the short-edge cone comparisons of the two
triangles. The outer corners are pasted through their common diagonal.
That pasting uses the specified gluing identification explicitly.

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

module SCT.VolumeI.Chapter02.Section02.GluedSquareCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.GluedSquareArrows 𝒯 M ℱ P I E S Q public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus 𝒯 using (coneIso-compose)
import SCT.VolumeI.Chapter02.Section02.SquareBoundaryCones as Boundaries
import SCT.VolumeI.Chapter02.Section02.PresentationSubstitution as Presentations
import SCT.VolumeI.Chapter02.Section02.CommonRestrictionDiagonal as Diagonal
import SCT.VolumeI.Chapter02.Section02.FramedCornerPasting as Pasting
open import SCT.VolumeI.Chapter02.Section01.SquareShape 𝒯 M ℱ P I E
  using (j₀; j₁; diagonal; j₀-diagonal; j₁-diagonal)

module Corners {Γ C : CAT} {x y z w : MAP Γ C}
  {top : MorphismExpression x y} {right : MorphismExpression y z}
  {left : MorphismExpression x w} {bottom : MorphismExpression w z}
  {diag : MorphismExpression x z}
  (upper : CompositePresentation top right diag)
  (lower : CompositePresentation left bottom diag) where
  module Arrows = At upper lower
  module G = Arrows.Glued
  module U = Arrows.Upper
  module L = Arrows.Lower
  module UC = Presentations.Corners 𝒯 M ℱ P I E S G.upper-presentation
  module LC = Presentations.Corners 𝒯 M ℱ P I E S G.lower-presentation
  module B = Boundaries.At 𝒯 M ℱ P I E G.square
  module D = Diagonal.At 𝒯 M ℱ P {C = C} d₁ j₀ j₁ diagonal j₀-diagonal j₁-diagonal
  module DF = D.Family G.square
  module Top = MorphismExpression top
  module Right = MorphismExpression right
  module Left = MorphismExpression left
  module Bottom = MorphismExpression bottom
  module Diag = MorphismExpression diag

  upper-middle = coneIso-compose U.short-edges B.UpperMiddle.comparison
  lower-middle = coneIso-compose L.short-edges B.LowerMiddle.comparison
  upper-source = coneIso-compose UC.source-cone-comparison B.UpperSource.comparison
  lower-source = coneIso-compose LC.source-cone-comparison B.LowerSource.comparison
  upper-target = coneIso-compose UC.target-cone-comparison B.UpperTarget.comparison
  lower-target = coneIso-compose LC.target-cone-comparison B.LowerTarget.comparison

  top-source-frame = B.UpperSource.Framing.Restricted.right-frame
  top-target-frame = B.UpperMiddle.Framing.Restricted.left-frame
  right-source-frame = B.UpperMiddle.Framing.Restricted.right-frame
  right-target-frame = B.UpperTarget.Framing.Restricted.right-frame
  left-source-frame = B.LowerSource.Framing.Restricted.right-frame
  left-target-frame = B.LowerMiddle.Framing.Restricted.left-frame
  bottom-source-frame = B.LowerMiddle.Framing.Restricted.right-frame
  bottom-target-frame = B.LowerTarget.Framing.Restricted.right-frame
  diagonal-source-frame = B.UpperSource.Framing.Restricted.left-frame
  diagonal-target-frame = B.UpperTarget.Framing.Restricted.left-frame

  abstract
    common-diagonal : ConeIso.leftIso lower-source =₂ ConeIso.leftIso upper-source
    common-diagonal = isoComp-cong G.diagonal-compatible (idIso DF.left) ∙
      (isoComp-assoc-at (ExpressionIso.comparison L.long-edge) G.specified-matching DF.left) ⁻¹ ∙
      isoComp-cong (idIso (ExpressionIso.comparison L.long-edge)) (DF.comparison ⁻¹)

  module Source = Pasting.ThroughCommon 𝒯 M ℱ P
    diagonal-source-frame top-source-frame left-source-frame
    Diag.source-frame Top.source-frame Left.source-frame
    upper-source lower-source common-diagonal
  module Target = Pasting.ThroughCommon 𝒯 M ℱ P
    diagonal-target-frame bottom-target-frame right-target-frame
    Diag.target-frame Bottom.target-frame Right.target-frame
    lower-target upper-target (common-diagonal ⁻¹)

  corner₀₀ = Source.comparison
  corner₀₁ = upper-middle
  corner₁₀ = Pasting.swap-framed 𝒯 M ℱ P left-target-frame bottom-source-frame
    Left.target-frame Bottom.source-frame lower-middle
  corner₁₁ = Target.comparison
```
