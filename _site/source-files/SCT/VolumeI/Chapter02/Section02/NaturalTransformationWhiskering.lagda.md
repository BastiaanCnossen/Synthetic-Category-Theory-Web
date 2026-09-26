# Whiskering natural transformations with common endpoint choices

The underlying actions are the existing `funPre` and `funPost` functors.
Their endpoint frames use the same named-composite comparison at every
vertex. The comparison with the internal composition action is a full
`ExpressionIso`, so subsequent pasting preserves these frames.

This is an explicit choice of the endpoint identifications left implicit
in the manuscript. It is not an assertion that these identifications
are definitionally equal to other currying or naming comparisons.

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

module SCT.VolumeI.Chapter02.Section02.NaturalTransformationWhiskering
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.FixedCoordinateExpressions as Fixed
import SCT.VolumeI.Chapter02.Section02.InternalComposition as Internal

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.WhiskeringComparisonTransfer 𝒯 M ℱ P I E S using (module Transfer)

module Pre {B C D : CAT} (u : MAP B C) {F G : MAP C D}
  (α : MorphismExpression (nameFun F) (nameFun G)) where
  private
    module InternalAction = Internal.At 𝒯 M ℱ B C D
  private
    module Coordinate = Fixed.FixRight 𝒯 M ℱ P I E S {A = Fun C D} {B = Fun B C} (nameFun u)
  private
    module Unary = InternalAction.FixRight u
  paired : MorphismExpression (pair (nameFun F) (nameFun u)) (pair (nameFun G) (nameFun u))
  paired = pair-expression α (identity-expression (nameFun u))
  private
    module Compared = Transfer {A = Fun C D} {B = Fun C D × Fun B C} {C = Fun B D}
      InternalAction.composeFunctor Coordinate.insertion (funPre {D = D} u) Unary.comparison
      {x = nameFun F} {x′ = nameFun G}
      {y = pair (nameFun F) (nameFun u)} {y′ = pair (nameFun G) (nameFun u)}
      {z = nameFun (F ∘ u)} {z′ = nameFun (G ∘ u)}
      α paired (Coordinate.frame (nameFun F)) (Coordinate.frame (nameFun G))
      (InternalAction.Named.comparison F u) (InternalAction.Named.comparison G u)
      (Coordinate.Arrow.comparison α)
  action : MorphismExpression (nameFun (F ∘ u)) (nameFun (G ∘ u))
  action = Compared.action
  comparison : ExpressionIso
    (retarget-expression (post-expression InternalAction.composeFunctor paired)
      (InternalAction.Named.comparison F u) (InternalAction.Named.comparison G u)) action
  comparison = Compared.comparison

module Post {B C D : CAT} (F : MAP C D) {u v : MAP B C}
  (β : MorphismExpression (nameFun u) (nameFun v)) where
  private
    module InternalAction = Internal.At 𝒯 M ℱ B C D
  private
    module Coordinate = Fixed.FixLeft 𝒯 M ℱ P I E S {A = Fun C D} {B = Fun B C} (nameFun F)
  private
    module Unary = InternalAction.FixLeft F
  paired : MorphismExpression (pair (nameFun F) (nameFun u)) (pair (nameFun F) (nameFun v))
  paired = pair-expression (identity-expression (nameFun F)) β
  private
    module Compared = Transfer {A = Fun B C} {B = Fun C D × Fun B C} {C = Fun B D}
      InternalAction.composeFunctor Coordinate.insertion (funPost {C = B} F) Unary.comparison
      {x = nameFun u} {x′ = nameFun v}
      {y = pair (nameFun F) (nameFun u)} {y′ = pair (nameFun F) (nameFun v)}
      {z = nameFun (F ∘ u)} {z′ = nameFun (F ∘ v)}
      β paired (Coordinate.frame (nameFun u)) (Coordinate.frame (nameFun v))
      (InternalAction.Named.comparison F u) (InternalAction.Named.comparison F v)
      (Coordinate.Arrow.comparison β)
  action : MorphismExpression (nameFun (F ∘ u)) (nameFun (F ∘ v))
  action = Compared.action
  comparison : ExpressionIso
    (retarget-expression (post-expression InternalAction.composeFunctor paired)
      (InternalAction.Named.comparison F u) (InternalAction.Named.comparison F v)) action
  comparison = Compared.comparison

pre-whisker : {B C D : CAT} (u : MAP B C) {F G : MAP C D} →
  MorphismExpression (nameFun F) (nameFun G) → MorphismExpression (nameFun (F ∘ u)) (nameFun (G ∘ u))
pre-whisker {B} {C} {D} u {F} {G} α = Pre.action {B} {C} {D} u {F} {G} α
post-whisker : {B C D : CAT} (F : MAP C D) {u v : MAP B C} →
  MorphismExpression (nameFun u) (nameFun v) → MorphismExpression (nameFun (F ∘ u)) (nameFun (F ∘ v))
post-whisker {B} {C} {D} F {u} {v} β = Post.action {B} {C} {D} F {u} {v} β
```
