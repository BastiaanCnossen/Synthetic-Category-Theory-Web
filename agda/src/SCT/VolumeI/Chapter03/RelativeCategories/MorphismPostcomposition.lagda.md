# Postcomposition detects the over-base condition

Postcomposing by any specified functor over the base preserves and
reflects whether a transformation lies over the base. This reflects only
the base condition, not identifications or invertibility of transformations.

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

module SCT.VolumeI.Chapter03.RelativeCategories.MorphismPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting as Pasting

module At {C D E′ B : CAT} {p : MAP C B} {q : MAP D B} {b : MAP E′ B}
  (t : FunctorOver q b) {u v : FunctorOver p q}
  (α : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v)) where
  private
    module T = FunctorLift t
    module U = FunctorLift u
    module V = FunctorLift v
    module TU = FunctorLift (compose-over t u)
    module TV = FunctorLift (compose-over t v)
    module Paste = Pasting.At 𝒯 M ℱ P I E T.lift b q T.comparison α

  abstract
    comparison : ExpressionIso
      (retarget-expression (post-expression b (post-expression T.lift α)) TU.comparison TV.comparison)
      (retarget-expression (post-expression q α) U.comparison V.comparison)
    comparison = expressionIso-compose (retarget-expressionIso Paste.comparison U.comparison V.comparison)
      (expressionIso-inverse (retarget-assoc (post-expression b (post-expression T.lift α))
        Paste.source-change Paste.target-change U.comparison V.comparison))

    preserves : Over.IsOver p q u v α →
      Over.IsOver p b (compose-over t u) (compose-over t v) (post-expression T.lift α)
    preserves over = expressionIso-compose over comparison

    reflects : Over.IsOver p b (compose-over t u) (compose-over t v) (post-expression T.lift α) →
      Over.IsOver p q u v α
    reflects over = expressionIso-compose over (expressionIso-inverse comparison)
```
