# A glued square as a morphism in the arrow category

The vertical morphism goes from the specified left side to the specified
right side. Its evaluated arrows compare with the specified top and bottom
sides. The construction retains the actual restriction compositors and
the reflected comparisons from double currying.

The two final comparisons here are comparisons of arrows.
`GluedSquareCorners` proves their four corner equations, and
`GluedFramedSquares` assembles the resulting `FramedSquare`.

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

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.GluedSquareArrows
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.GluedCompositePresentations 𝒯 M ℱ P I E S Q public
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareShape 𝒯 M ℱ P I E
  using (j₀; j₁; bottom-boundary; top-boundary)
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (preComp; preCong)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurrying as Currying
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates 𝒯 M ℱ using (coinsert)

top-horizontal : (j₀ ∘ d₂) =₁ (coinsert zero)
top-horizontal = pair-cong s₀-d₂ s₁-d₂ ∙ pair-pre s₀ s₁ d₂
bottom-horizontal : (j₁ ∘ d₀) =₁ (coinsert one)
bottom-horizontal = pair-cong s₁-d₀ s₀-d₀ ∙ pair-pre s₁ s₀ d₀

restriction-edge : {Γ A B D C : CAT} (d : MAP A B) (j : MAP B D)
  {r : MAP A D} (α : (j ∘ d) =₁ r) (W : MAP Γ (Fun D C)) →
  (funPre r ∘ W) =₁ (funPre d ∘ (funPre j ∘ W))
restriction-edge d j α W = comp-assoc W (funPre j) (funPre d) ∙
  (((preComp d j ▷ W) ⁻¹) ∙ (preCong α ▷ W) ⁻¹)

module At {Γ C : CAT} {x y z w : MAP Γ C}
  {top : MorphismExpression x y} {right : MorphismExpression y z}
  {left : MorphismExpression x w} {bottom : MorphismExpression w z}
  {diagonal : MorphismExpression x z}
  (upper : CompositePresentation top right diagonal)
  (lower : CompositePresentation left bottom diagonal) where
  module Glued = Glue upper lower
  module Curried = Currying.At 𝒯 M ℱ Glued.square
  module Upper = CompositePresentation Glued.upper-presentation
  module Lower = CompositePresentation Glued.lower-presentation

  left-side : (funPre (insert zero) ∘ Glued.square) =₁ MorphismExpression.arrow left
  left-side = ConeIso.leftIso Lower.short-edges ∙ restriction-edge d₂ j₁ bottom-boundary Glued.square
  right-side : (funPre (insert one) ∘ Glued.square) =₁ MorphismExpression.arrow right
  right-side = ConeIso.rightIso Upper.short-edges ∙ restriction-edge d₀ j₀ top-boundary Glued.square
  top-side : (funPre (coinsert zero) ∘ Glued.square) =₁ MorphismExpression.arrow top
  top-side = ConeIso.leftIso Upper.short-edges ∙ restriction-edge d₂ j₀ top-horizontal Glued.square
  bottom-side : (funPre (coinsert one) ∘ Glued.square) =₁ MorphismExpression.arrow bottom
  bottom-side = ConeIso.rightIso Lower.short-edges ∙ restriction-edge d₀ j₁ bottom-horizontal Glued.square

  vertical-expression : MorphismExpression (MorphismExpression.arrow left) (MorphismExpression.arrow right)
  vertical-expression = record
    { arrow = Curried.nested
    ; source-frame = left-side ∙ Curried.Vertical.boundary zero
    ; target-frame = right-side ∙ Curried.Vertical.boundary one }

  top-comparison : MorphismExpression.arrow (post-expression ev₀ vertical-expression) =₁ MorphismExpression.arrow top
  top-comparison = top-side ∙ Curried.Horizontal.comparison zero
  bottom-comparison : MorphismExpression.arrow (post-expression ev₁ vertical-expression) =₁ MorphismExpression.arrow bottom
  bottom-comparison = bottom-side ∙ Curried.Horizontal.comparison one
```
