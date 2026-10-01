# Gluing composite presentations along their specified diagonal

Two presentations of the same diagonal determine a square family. The
comparison supplied by the square axiom retains the identification along
that diagonal, as well as the three vertices of each restricted triangle.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.GluedCompositePresentations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PresentationComparisons 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareShape 𝒯 M ℱ P I E using (j₀; j₁; gluing-square)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (functorOut)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareFamilies as Squares

module Glue {Γ C : CAT} {x y z w : MAP Γ C}
  {top : MorphismExpression x y} {right : MorphismExpression y z}
  {left : MorphismExpression x w} {bottom : MorphismExpression w z}
  {diagonal : MorphismExpression x z}
  (upper : CompositePresentation top right diagonal)
  (lower : CompositePresentation left bottom diagonal) where
  module Upper = CompositePresentation upper
  module Lower = CompositePresentation lower
  module Families = Squares.Families 𝒯 M ℱ P I E Q C

  upper-long = ExpressionIso.comparison Upper.long-edge
  lower-long = ExpressionIso.comparison Lower.long-edge

  triangles : Cone (edge₁ {C}) edge₁ Γ
  triangles = record
    { left = Upper.triangle ; right = Lower.triangle
    ; match = lower-long ⁻¹ ∙ upper-long }

  square : MAP Γ (Fun ([1] × [1]) C)
  square = Families.square-in triangles

  gluing-comparison : ConeIso (conePre square (functorOut gluing-square C)) triangles
  gluing-comparison = Families.square-in-β triangles

  module UpperRestriction = ChangeTriangle upper (ConeIso.leftIso gluing-comparison)
    using (presentation)
  module LowerRestriction = ChangeTriangle lower (ConeIso.rightIso gluing-comparison)
    using (presentation)

  upper-presentation : CompositePresentation top right diagonal
  upper-presentation = UpperRestriction.presentation

  lower-presentation : CompositePresentation left bottom diagonal
  lower-presentation = LowerRestriction.presentation

  specified-matching = Cone.match (conePre square (functorOut gluing-square C))

  -- The same diagonal comparison is retained across the specified matching.
  diagonal-compatible :
    (ExpressionIso.comparison (CompositePresentation.long-edge lower-presentation) ∙ specified-matching) =₂
    ExpressionIso.comparison (CompositePresentation.long-edge upper-presentation)
  diagonal-compatible =
    (vertex-from-corner lower-long upper-long
      (edge₁ ◁ ConeIso.leftIso gluing-comparison)
      ((edge₁ ◁ ConeIso.rightIso gluing-comparison) ∙ specified-matching)
      (ConeIso.compatible gluing-comparison)) ⁻¹ ∙
    isoComp-assoc-at lower-long (edge₁ ◁ ConeIso.rightIso gluing-comparison) specified-matching
```
