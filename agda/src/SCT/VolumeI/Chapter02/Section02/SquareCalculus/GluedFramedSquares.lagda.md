# A glued square with all four endpoint equations

The four geometric corner comparisons become the source and target
equations of its top and bottom arrows. The resulting framed square can
be composed in the arrow category.

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

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.GluedFramedSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.ArrowCategorySquares 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.GluedSquareCorners as Corners
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.FramedSquareEndpoints as Endpoints

module At {Γ C : CAT} {x y z w : MAP Γ C}
  {top : MorphismExpression x y} {right : MorphismExpression y z}
  {left : MorphismExpression x w} {bottom : MorphismExpression w z}
  {diag : MorphismExpression x z}
  (upper : CompositePresentation top right diag)
  (lower : CompositePresentation left bottom diag) where
  module K = Corners.Corners 𝒯 M ℱ P I E S Q upper lower
  module A = K.Arrows
  module Top = MorphismExpression top
  module Right = MorphismExpression right
  module Left = MorphismExpression left
  module Bottom = MorphismExpression bottom
  module V₀₀ = Endpoints.At 𝒯 M ℱ P I E S A.Glued.square zero zero Top.source-frame Left.source-frame
  module V₀₁ = Endpoints.At 𝒯 M ℱ P I E S A.Glued.square zero one Top.target-frame Right.source-frame
  module V₁₀ = Endpoints.At 𝒯 M ℱ P I E S A.Glued.square one zero Bottom.source-frame Left.target-frame
  module V₁₁ = Endpoints.At 𝒯 M ℱ P I E S A.Glued.square one one Bottom.target-frame Right.target-frame

  square : FramedSquare top right left bottom
  square = record
    { vertical = A.vertical-expression
    ; top-edge = record
      { comparison = A.top-comparison
      ; source-compatible = V₀₀.FromCone.compatible K.corner₀₀
      ; target-compatible = V₀₁.FromCone.compatible K.corner₀₁ }
    ; bottom-edge = record
      { comparison = A.bottom-comparison
      ; source-compatible = V₁₀.FromCone.compatible K.corner₁₀
      ; target-compatible = V₁₁.FromCone.compatible K.corner₁₁ } }
```
