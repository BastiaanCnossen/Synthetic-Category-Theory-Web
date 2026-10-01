# Interchange for a functor of two variables

Each side changes one input and fixes the other by its identity morphism.
Composition in products and the unit laws identify both routes with the
image of the paired morphism. All comparisons preserve the four chosen
vertices.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section02.ProductInterchange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (product-composition; pair-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit; right-unit)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S using (post-composition)

module At {Γ A B C : CAT} (K : MAP (A × B) C)
  {x x′ : MAP Γ A} {y y′ : MAP Γ B}
  (α : MorphismExpression x x′) (β : MorphismExpression y y′) where
  top = post-expression K (pair-expression α (identity-expression y))
  right = post-expression K (pair-expression (identity-expression x′) β)
  left = post-expression K (pair-expression (identity-expression x) β)
  bottom = post-expression K (pair-expression α (identity-expression y′))
  diagonal = post-expression K (pair-expression α β)

  first-route : ExpressionIso (compose-expression top right) diagonal
  first-route = expressionIso-compose
    (post-expressionIso K (pair-expression-cong (right-unit α) (left-unit β)))
    (expressionIso-compose
      (post-expressionIso K (product-composition α (identity-expression x′) (identity-expression y) β))
      (post-composition K (pair-expression α (identity-expression y)) (pair-expression (identity-expression x′) β)))

  second-route : ExpressionIso (compose-expression left bottom) diagonal
  second-route = expressionIso-compose
    (post-expressionIso K (pair-expression-cong (left-unit α) (right-unit β)))
    (expressionIso-compose
      (post-expressionIso K (product-composition (identity-expression x) α β (identity-expression y′)))
      (post-composition K (pair-expression (identity-expression x) β) (pair-expression α (identity-expression y′))))

  comparison : ExpressionIso (compose-expression top right) (compose-expression left bottom)
  comparison = expressionIso-compose (expressionIso-inverse second-route) first-route
```
