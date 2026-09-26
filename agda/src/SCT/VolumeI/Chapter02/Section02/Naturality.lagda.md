# The naturality square

Apply the diagram of a transformation to a morphism. Its source and
target are the two evaluated transformations; the endpoint adapter
identifies its other sides with the images of the original morphism.
The two triangles give the displayed naturality identification.

The parameter category `Γ` is arbitrary and absolute. In particular,
the theorem applies to a family of morphisms over another category.

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

module SCT.VolumeI.Chapter02.Section02.Naturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.ArrowCategorySquares 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I using (expressionIso-inverse)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting as Pasting
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.FramedSquareCommutativity as Commutativity

module At {Γ C D : CAT} {F G : MAP C D} (α : MorphismExpression F G)
  {x y : MAP Γ C} (u : MorphismExpression x y) where
  module A = MorphismExpression α
  top = post-expression F u
  right = restrict-expression α y
  left = restrict-expression α x
  bottom = post-expression G u

  square : FramedSquare top right left bottom
  square = record
    { vertical = post-expression A.arrow u
    ; top-edge = Pasting.At.comparison 𝒯 M ℱ P I E A.arrow ev₀ F A.source-frame u
    ; bottom-edge = Pasting.At.comparison 𝒯 M ℱ P I E A.arrow ev₁ G A.target-frame u }

  comparison : ExpressionIso
    (compose-expression left bottom) (compose-expression top right)
  comparison = expressionIso-inverse (Commutativity.At.comparison 𝒯 M ℱ P I E S square)

naturality : {Γ C D : CAT} {F G : MAP C D} (α : MorphismExpression F G)
  {x y : MAP Γ C} (u : MorphismExpression x y) →
  ExpressionIso
    (compose-expression (restrict-expression α x) (post-expression G u))
    (compose-expression (post-expression F u) (restrict-expression α y))
naturality = At.comparison
```
