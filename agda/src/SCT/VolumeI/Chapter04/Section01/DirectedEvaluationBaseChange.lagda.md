# Directed evaluation under base change

A specified pullback square induces a pullback square of directed source
evaluations and one of directed target evaluations. We construct the
induced map by the one-sided pullback presentation, retaining its entire
cone comparison. This is `lem:Directed_Evaluation_And_Pullback` for that
universal choice of the induced map.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.DirectedEvaluationBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
import SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointPullbacks as Endpoints
import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion as Comparisons
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationBaseChange as BaseChange

module At {C D B X : CAT} {f : MAP C B} {v : MAP D B}
  (s : Cone f v X) (es : IsPullback s) where
  u = Cone.left s
  p = Cone.right s
  module Old = Evaluation f using (directed-ev₀; directed-ev₁)
  module New = Evaluation p using (directed-ev₀; directed-ev₁)
  module OldComparison = Comparisons.Criterion 𝒯 M ℱ P I f using (source-comparison; target-comparison)
  module NewComparison = Comparisons.Criterion 𝒯 M ℱ P I p using (source-comparison; target-comparison)

  module Source where
    module A = Endpoints.Source 𝒯 M ℱ P I p using (square; square-isPullback)
    module B₀ = Endpoints.Source 𝒯 M ℱ P I f using (square; square-isPullback)
    module Change = BaseChange.At 𝒯 M ℱ P zero s es A.square A.square-isPullback B₀.square B₀.square-isPullback
      using (h; βh; module Factors)
    map = Change.h
    map-comparison = Change.βh
    module Result = Change.Factors New.directed-ev₀ Old.directed-ev₀
      NewComparison.source-comparison OldComparison.source-comparison using (square; square-isPullback)
    open Result public using (square; square-isPullback)

  module Target where
    module A = Endpoints.Target 𝒯 M ℱ P I p using (square; square-isPullback)
    module B₀ = Endpoints.Target 𝒯 M ℱ P I f using (square; square-isPullback)
    module Change = BaseChange.At 𝒯 M ℱ P one s es A.square A.square-isPullback B₀.square B₀.square-isPullback
      using (h; βh; module Factors)
    map = Change.h
    map-comparison = Change.βh
    module Result = Change.Factors New.directed-ev₁ Old.directed-ev₁
      NewComparison.target-comparison OldComparison.target-comparison using (square; square-isPullback)
    open Result public using (square; square-isPullback)
```
