# Adjunctions induced by postcomposition

Postcomposition carries an adjunction to an adjunction on functor
categories. The unit and counit are the chosen curried component diagrams.
Their actual triangle identities follow by evaluating with common
endpoint frames and reflecting the original component triangles.

This proves the postcomposition assertion of
`prop:Adjunction_On_Functor_Categories`.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PostcompositionAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PostcompositionTriangleLegs as Legs
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentTriangles as Triangles
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingTriangleReflection as Reflection

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module Evaluated = Legs.At 𝒯 M ℱ P I E S adj K
  module B = Evaluated.B
  module Original = Triangles.Components 𝒯 M ℱ P I E S adj
  module Left = Reflection.At 𝒯 M ℱ P I E S B.Components.left-unit B.Components.left-counit
    Evaluated.βl Evaluated.LeftMiddle.middle
  module Right = Reflection.At 𝒯 M ℱ P I E S B.Components.right-unit B.Components.right-counit
    Evaluated.βr Evaluated.RightMiddle.middle

  abstract
    value : Adjunction (funPost {C = K} l) (funPost {C = K} r)
    value = record
      { unit = B.unit
      ; counit = B.counit
      ; left-triangle = Left.reflect (expressionIso-compose (Original.left-triangle-at Evaluated.e)
          (compose-expression-cong Evaluated.left-unit Evaluated.left-counit))
      ; right-triangle = Right.reflect (expressionIso-compose (Original.right-triangle-at Evaluated.d)
          (compose-expression-cong Evaluated.right-unit Evaluated.right-counit)) }

    unit-comparison : ExpressionIso (Adjunction.unit value) B.unit
    unit-comparison = expressionIso-id B.unit

    counit-comparison : ExpressionIso (Adjunction.counit value) B.counit
    counit-comparison = expressionIso-id B.counit
```
