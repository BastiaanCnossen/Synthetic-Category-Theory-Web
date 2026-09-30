# Triangles over a base

When a composite is the identity, either leg lies over the base if the
other does. Applying the base functor and the specified endpoint frames
reduces this to the unit laws for morphism composition.

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

module SCT.VolumeI.Chapter03.RelativeCategories.MorphismTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S
  using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S
  using (left-unit; right-unit)

module Triangle {C D B : CAT} {p : MAP C B} {q : MAP D B} {u v : FunctorOver p q}
  (α : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v))
  (β : MorphismExpression (FunctorLift.lift v) (FunctorLift.lift u))
  (triangle : ExpressionIso (compose-expression α β) (identity-expression (FunctorLift.lift u))) where
  private
    module U = FunctorLift u
    module V = FunctorLift v
  first = retarget-expression (post-expression q α) U.comparison V.comparison
  second = retarget-expression (post-expression q β) V.comparison U.comparison

  abstract
    image-triangle : ExpressionIso (compose-expression first second) (identity-expression p)
    image-triangle = expressionIso-compose (Over.identity-isOver p q u)
      (expressionIso-compose (retarget-expressionIso (post-expressionIso q triangle) U.comparison U.comparison)
        (expressionIso-compose (retarget-expressionIso (post-composition q α β) U.comparison U.comparison)
          (retarget-composition (post-expression q α) (post-expression q β)
            U.comparison V.comparison U.comparison)))

    first-over : Over.IsOver p q v u β → Over.IsOver p q u v α
    first-over over = expressionIso-compose image-triangle
      (expressionIso-compose (compose-expression-cong (expressionIso-id first) (expressionIso-inverse over))
        (expressionIso-inverse (right-unit first)))

    second-over : Over.IsOver p q u v α → Over.IsOver p q v u β
    second-over over = expressionIso-compose image-triangle
      (expressionIso-compose (compose-expression-cong (expressionIso-inverse over) (expressionIso-id second))
        (expressionIso-inverse (left-unit second)))
```
