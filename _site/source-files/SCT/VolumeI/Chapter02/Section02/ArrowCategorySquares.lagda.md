# Composing squares in the arrow category

A framed square is a morphism between its two vertical arrows. Its top
and bottom comparisons include the four corner equations. Composition
in the arrow category composes the horizontal edges, with their specified
endpoints, by preservation under evaluation.

This is the algebraic part of the associativity construction. Converting
a square family into such a framed square is a separate geometric step.

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

module SCT.VolumeI.Chapter02.Section02.ArrowCategorySquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.PostcompositionPresentations 𝒯 M ℱ P I E S using (post-composition)

record FramedSquare {Γ C : CAT} {x y z w : MAP Γ C}
  (top : MorphismExpression x y) (right : MorphismExpression y z)
  (left : MorphismExpression x w) (bottom : MorphismExpression w z) : Set m where
  field
    vertical : MorphismExpression (MorphismExpression.arrow left) (MorphismExpression.arrow right)
    top-edge : ExpressionIso
      (retarget-expression (post-expression ev₀ vertical)
        (MorphismExpression.source-frame left) (MorphismExpression.source-frame right)) top
    bottom-edge : ExpressionIso
      (retarget-expression (post-expression ev₁ vertical)
        (MorphismExpression.target-frame left) (MorphismExpression.target-frame right)) bottom

-- Evaluation followed by endpoint adjustment preserves composition.
framed-evaluation-composition : {Γ C : CAT} {l k r : MAP Γ (Ar C)}
  (A : MorphismExpression l k) (B : MorphismExpression k r)
  (v : MAP (Ar C) C) {x y z : MAP Γ C}
  (α : (v ∘ l) =₁ x) (β : (v ∘ k) =₁ y) (γ : (v ∘ r) =₁ z) →
  ExpressionIso
    (retarget-expression (post-expression v (compose-expression A B)) α γ)
    (compose-expression (retarget-expression (post-expression v A) α β)
      (retarget-expression (post-expression v B) β γ))
framed-evaluation-composition A B v α β γ = expressionIso-inverse
  (expressionIso-compose (retarget-expressionIso (post-composition v A B) α γ)
    (retarget-composition (post-expression v A) (post-expression v B) α β γ))

module Compose {Γ C : CAT} {x₀ x₁ x₂ y₀ y₁ y₂ : MAP Γ C}
  {top₀ : MorphismExpression x₀ x₁} {top₁ : MorphismExpression x₁ x₂}
  {bottom₀ : MorphismExpression y₀ y₁} {bottom₁ : MorphismExpression y₁ y₂}
  {left : MorphismExpression x₀ y₀} {middle : MorphismExpression x₁ y₁}
  {right : MorphismExpression x₂ y₂}
  (A : FramedSquare top₀ middle left bottom₀)
  (B : FramedSquare top₁ right middle bottom₁) where
  module A₀ = FramedSquare A
  module B₀ = FramedSquare B
  module L = MorphismExpression left
  module K = MorphismExpression middle
  module R = MorphismExpression right

  square : FramedSquare (compose-expression top₀ top₁) right left
    (compose-expression bottom₀ bottom₁)
  square = record
    { vertical = compose-expression A₀.vertical B₀.vertical
    ; top-edge = expressionIso-compose (compose-expression-cong A₀.top-edge B₀.top-edge)
        (framed-evaluation-composition A₀.vertical B₀.vertical ev₀ L.source-frame K.source-frame R.source-frame)
    ; bottom-edge = expressionIso-compose (compose-expression-cong A₀.bottom-edge B₀.bottom-edge)
        (framed-evaluation-composition A₀.vertical B₀.vertical ev₁ L.target-frame K.target-frame R.target-frame) }
```
