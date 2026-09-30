# Evaluating the pullback of dependent products

Pull back the two induced functors, evaluate its two projections, and
use the original pullback. The matching is obtained by uncurrying the
specified relative pullback matching, including its triangle over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.DependentProductEvaluationNaturality 𝒯 M ℱ P using (module Naturality)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackLifting 𝒯 M ℱ P using (module Lift)

module Evaluation {S T C D E : CAT} (p : MAP S T)
  {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (ΠE : DependentProduct p h)
  (u : FunctorOver f h) (v : FunctorOver g h) where
  module R = RelativePullback u v using (category; projection; first; second; match-over)
  iu = Induced.over p f h ΠC ΠE u
  iv = Induced.over p g h ΠD ΠE v
  module Q = RelativePullback iu iv using (category; projection; first; second; match-over)
  module C = Currying p f ΠC using (evaluate)
  module D = Currying p g ΠD using (evaluate)
  module E = Currying p h ΠE using (evaluate)
  first = C.evaluate Q.first
  second = D.evaluate Q.second

  abstract
    matching : FunctorOverIso (compose-over u first) (compose-over v second)
    matching = compose-iso-over (Naturality.comparison p g h ΠD ΠE v Q.second)
      (compose-iso-over
        (postwhisker-over (DependentProduct.evaluation ΠE) (Change.Identification.comparison p Q.match-over))
        (inverse-iso-over (Naturality.comparison p f h ΠC ΠE u Q.first)))

  module Lifted = Lift u v first second matching
    using (over; first-comparison; second-comparison; cone; cone-comparison)
  evaluation : FunctorOver (pullback₂ {f = Q.projection} {p}) R.projection
  evaluation = Lifted.over
```
