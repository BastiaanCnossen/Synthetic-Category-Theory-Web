# The pullback square for composition of directed evaluation

Successive pullback cancellation constructs the square in
`lem:Directed_Evaluation_And_Composition`, for either endpoint. Its
maps are chosen by the one-sided universal properties. The comparison
of the upper composite with directed evaluation of gf, including the
triangle in the manuscript, remains a separate obligation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.CompositionPullback
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
import SCT.VolumeI.Chapter01.Section06.Pasting.FactoredComposition as Factored
import SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointPullbacks as Endpoints
import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion as Comparisons

module At {A B C : CAT} (f : MAP A B) (g : MAP B C) where
  module Eval = Evaluation g using (directed-ev₀; directed-ev₁)
  module Compare = Comparisons.Criterion 𝒯 M ℱ P I g using (source-comparison; target-comparison)

  module Source where
    module G = Endpoints.Source 𝒯 M ℱ P I g using (square; square-isPullback)
    module GF = Endpoints.Source 𝒯 M ℱ P I (g ∘ f) using (square; square-isPullback)
    module F = Endpoints.Source 𝒯 M ℱ P I f using (square; square-isPullback)
    module Outer = Factored.At 𝒯 P f g ev₀
      (coneSwap G.square) (pullback-swap G.square G.square-isPullback)
      (coneSwap GF.square) (pullback-swap GF.square GF.square-isPullback)
      using (h; h-comparison; module Factor)
    right-map = Outer.h
    right-comparison = Outer.h-comparison
    module Result = Outer.Factor Eval.directed-ev₀ ev₀
      (ConeIso.rightIso Compare.source-comparison) F.square F.square-isPullback
      using (map; map-comparison; square; square-isPullback)
    open Result public

  module Target where
    module G = Endpoints.Target 𝒯 M ℱ P I g using (square; square-isPullback)
    module GF = Endpoints.Target 𝒯 M ℱ P I (g ∘ f) using (square; square-isPullback)
    module F = Endpoints.Target 𝒯 M ℱ P I f using (square; square-isPullback)
    module Outer = Factored.At 𝒯 P f g ev₁
      (coneSwap G.square) (pullback-swap G.square G.square-isPullback)
      (coneSwap GF.square) (pullback-swap GF.square GF.square-isPullback)
      using (h; h-comparison; module Factor)
    right-map = Outer.h
    right-comparison = Outer.h-comparison
    module Result = Outer.Factor Eval.directed-ev₁ ev₁
      (ConeIso.rightIso Compare.target-comparison) F.square F.square-isPullback
      using (map; map-comparison; square; square-isPullback)
    open Result public
```
