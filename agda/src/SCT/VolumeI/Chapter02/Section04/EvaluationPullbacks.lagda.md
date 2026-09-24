# Evaluation on a functor-category pullback

The map of pullbacks induced by evaluation agrees with evaluation on
the pullback category itself. Both comparisons below concern whole
cones, so the specified matching identification is retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.EvaluationPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P
open import SCT.VolumeI.Chapter02.Section04.EvaluationCones 𝒯 M ℱ P

module EvaluatePullback {T C D E : CAT} (z : Obj-abs T) (f : MAP C E) (g : MAP D E) where
  module Evaluation = EvaluationCone z f g
  module FunctorSquare = FunctorPullback T f g
  original = pullbackCone f g
  middle = pullbackCone (funPost {C = T} f) (funPost g)

  comparison : ConeIso
    (conePre (Evaluation.Induced.pullbackMap ∘ FunctorSquare.comparison) original)
    (conePre (evaluate z) original)
  comparison = coneIso-compose (conePre-assoc (insert z) funEval original)
    (coneIso-compose (coneIso-pre (insert z) (MappedCone.Curried.comparison T original))
    (coneIso-compose (Evaluation.At.comparison FunctorSquare.square)
    (coneIso-compose (Evaluation.Act.map-iso FunctorSquare.comparison-computation)
    (coneIso-compose (coneIso-inverse (Evaluation.Act.map-pre FunctorSquare.comparison middle))
    (coneIso-compose (coneIso-pre FunctorSquare.comparison Evaluation.Induced.pullbackMap-β)
      (coneIso-inverse (conePre-assoc FunctorSquare.comparison Evaluation.Induced.pullbackMap original)))))))

  evaluation-comparison :
    (Evaluation.Induced.pullbackMap ∘ FunctorSquare.comparison) =₁ (evaluate z)
  evaluation-comparison = pullback-reflect _ _ comparison

  evaluation-isEquiv : IsEquiv Evaluation.Induced.pullbackMap →
    IsEquiv (evaluate {C = Pullback f g} z)
  evaluation-isEquiv e = equiv-transport evaluation-comparison
    (equiv-compose FunctorSquare.comparison Evaluation.Induced.pullbackMap
      FunctorSquare.comparison-isEquiv e)
```
