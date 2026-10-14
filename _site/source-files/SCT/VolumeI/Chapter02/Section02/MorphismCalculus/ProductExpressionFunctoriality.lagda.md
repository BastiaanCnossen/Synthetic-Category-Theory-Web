# Applying a product functor to paired transformations

A product functor acts separately on the two paired transformations.
The specified endpoint comparison is `productMap-pair`, including its
coordinate associators and product beta identifications.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFunctoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget; retarget-assoc)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting 𝒯 M ℱ P I E
  using (post-composite)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions as Pairs
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as Frames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPairing as Pairing

module At {Γ A B C D : CAT} (F : MAP A B) (G : MAP C D)
  {x y : MAP Γ A} {u v : MAP Γ C} (α : MorphismExpression x y) (β : MorphismExpression u v) where
  module Paired = Pairs.At 𝒯 M ℱ I α β
  paired = pair-expression α β
  module Action = Pairing.At 𝒯 M ℱ P I E S (F ∘ pr₁) (G ∘ pr₂) paired

  module Projection {Y Z : CAT} (π : MAP (A × C) Y) (H : MAP Y Z) {a b : MAP Γ Y}
    (τ : MorphismExpression a b) (p : (π ∘ pair x u) =₁ a) (q : (π ∘ pair y v) =₁ b)
    (given : ExpressionIso (retarget-expression (post-expression π paired) p q) τ) where
    source-change = (H ◁ p) ∙ comp-assoc (pair x u) π H
    target-change = (H ◁ q) ∙ comp-assoc (pair y v) π H
    abstract
      value : ExpressionIso (retarget-expression (post-expression (H ∘ π) paired) source-change target-change)
        (post-expression H τ)
      value = expressionIso-compose (post-expressionIso H given)
        (expressionIso-compose (expressionIso-inverse (post-retarget H (post-expression π paired) p q))
          (expressionIso-compose (retarget-expressionIso (post-composite π H paired) (H ◁ p) (H ◁ q))
            (expressionIso-inverse (retarget-assoc (post-expression (H ∘ π) paired)
              (comp-assoc (pair x u) π H) (comp-assoc (pair y v) π H) (H ◁ p) (H ◁ q)))))

  module First = Projection pr₁ F α (pair-β₁ x u) (pair-β₁ y v) Paired.first-projection
  module Second = Projection pr₂ G β (pair-β₂ x u) (pair-β₂ y v) Paired.second-projection
  module ProductFrames = Frames.At 𝒯 M ℱ I (post-expression (F ∘ pr₁) paired) (post-expression (G ∘ pr₂) paired)
    First.source-change First.target-change Second.source-change Second.target-change

  abstract
    value : ExpressionIso (retarget-expression (post-expression (productMap F G) paired)
      (productMap-pair F G x u) (productMap-pair F G y v))
      (pair-expression (post-expression F α) (post-expression G β))
    value = expressionIso-compose (pair-expression-cong First.value Second.value)
      (expressionIso-compose ProductFrames.value
        (expressionIso-compose (retarget-expressionIso Action.value
            (pair-cong First.source-change Second.source-change) (pair-cong First.target-change Second.target-change))
          (expressionIso-inverse (retarget-assoc (post-expression (productMap F G) paired)
            (pair-pre (F ∘ pr₁) (G ∘ pr₂) (pair x u)) (pair-pre (F ∘ pr₁) (G ∘ pr₂) (pair y v))
            (pair-cong First.source-change Second.source-change) (pair-cong First.target-change Second.target-change)))))
```
