# Composition of directed evaluation

For composable functors, directed evaluation of the composite factors
through directed evaluation of the first functor. The intervening map
is a base change of directed evaluation of the second functor. This
proves both the square and upper triangle in
`lem:Directed_Evaluation_And_Composition`, in both variances, for the
one-sided universal choices of the induced maps.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.DirectedEvaluationComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
import SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointPullbacks as Endpoints
import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion as Comparisons
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationCompositionComparison as Triangles

module At {A B C : CAT} (f : MAP A B) (g : MAP B C) where
  module F = Evaluation f using (directed-ev₀; directed-ev₁)
  module G = Evaluation g using (directed-ev₀; directed-ev₁)
  module GF = Evaluation (g ∘ f) using (directed-ev₀; directed-ev₁)
  module FComparison = Comparisons.Criterion 𝒯 M ℱ P I f using (source-comparison; target-comparison)
  module GComparison = Comparisons.Criterion 𝒯 M ℱ P I g using (source-comparison; target-comparison)
  module GFComparison = Comparisons.Criterion 𝒯 M ℱ P I (g ∘ f) using (source-comparison; target-comparison)

  module Source where
    private
      module Qf = Endpoints.Source 𝒯 M ℱ P I f using (square; square-isPullback)
      module Qg = Endpoints.Source 𝒯 M ℱ P I g using (square; square-isPullback)
      module Qgf = Endpoints.Source 𝒯 M ℱ P I (g ∘ f) using (square; square-isPullback)
      module Result = Triangles.At.Factors.Triangle 𝒯 M ℱ P zero f g
        Qg.square Qg.square-isPullback Qgf.square Qgf.square-isPullback
        G.directed-ev₀ GF.directed-ev₀ GComparison.source-comparison GFComparison.source-comparison
        Qf.square Qf.square-isPullback F.directed-ev₀ FComparison.source-comparison using (right-map; map; square; square-isPullback; triangle)
    open Result public using (right-map; map; square; square-isPullback; triangle)

  module Target where
    private
      module Qf = Endpoints.Target 𝒯 M ℱ P I f using (square; square-isPullback)
      module Qg = Endpoints.Target 𝒯 M ℱ P I g using (square; square-isPullback)
      module Qgf = Endpoints.Target 𝒯 M ℱ P I (g ∘ f) using (square; square-isPullback)
      module Result = Triangles.At.Factors.Triangle 𝒯 M ℱ P one f g
        Qg.square Qg.square-isPullback Qgf.square Qgf.square-isPullback
        G.directed-ev₁ GF.directed-ev₁ GComparison.target-comparison GFComparison.target-comparison
        Qf.square Qf.square-isPullback F.directed-ev₁ FComparison.target-comparison using (right-map; map; square; square-isPullback; triangle)
    open Result public using (right-map; map; square; square-isPullback; triangle)
```
