# Comparing relative pullback cones by uncurrying

Uncurrying gives an equivalence of the two cospans of relative functor
categories. Since both relative functor squares are pullbacks with their
specified matchings, this gives an equivalence of their cone points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullback-comparison; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as MappedCones
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.PullbackPreservation.DependentPullbackEvaluation 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.ProductCalculus.FunctorCategoryUncurrying 𝒯 M ℱ P using (module Uncurrying)
open import SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingNaturality 𝒯 M ℱ P using (module Natural)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackMatching 𝒯 M ℱ P using (module Matching)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.FunctorPullbackSquare 𝒯 M ℱ P using (module Square)

module PullbackComparison {S T C D E K : CAT} (p : MAP S T)
  {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (ΠC : DependentProduct p f) (ΠD : DependentProduct p g) (ΠE : DependentProduct p h)
  (u : FunctorOver f h) (v : FunctorOver g h) (k : MAP K T) where
  module Candidate = Evaluation p ΠC ΠD ΠE u v using (iu; iv; module Q; module R)
  k′ : MAP (Pullback k p) S
  k′ = pullback₂
  module UC = Uncurrying p f ΠC k using (functor; functor-isEquiv)
  module UD = Uncurrying p g ΠD k using (functor; functor-isEquiv)
  module UE = Uncurrying p h ΠE k using (functor; functor-isEquiv)
  module SourceU = Postcompose k Candidate.iu using (functor)
  module SourceV = Postcompose k Candidate.iv using (functor)
  module TargetU = Postcompose k′ u using (functor)
  module TargetV = Postcompose k′ v using (functor)
  cospan : CospanMap SourceU.functor SourceV.functor TargetU.functor TargetV.functor
  cospan = record
    { left = UC.functor ; right = UD.functor ; base = UE.functor
    ; leftSquare = (Natural.comparison p f h ΠC ΠE u k) ⁻¹
    ; rightSquare = (Natural.comparison p g h ΠD ΠE v k) ⁻¹ }
  source = Matching.cone k Candidate.iu Candidate.iv
  target = Matching.cone k′ u v
  abstract
    source-isPullback : IsPullback source
    source-isPullback = Square.isPullback k Candidate.iu Candidate.iv
    target-isPullback : IsPullback target
    target-isPullback = Square.isPullback k′ u v

  mapped = CospanMap.mapCone cospan source
  module Mapped = MappedCones.Mapped 𝒯 P cospan
    (degenerate-pullback UE.functor-isEquiv (MappedCones.rightSquareOf 𝒯 P cospan) UD.functor-isEquiv)
    source source-isPullback using (isPullback)
  module TargetCone = UniversalCone target target-isPullback using (factor; factor-β)
  forward : MAP (FunOver k Candidate.Q.projection) (FunOver k′ Candidate.R.projection)
  forward = TargetCone.factor mapped
  abstract
    mapped-isPullback : IsPullback mapped
    mapped-isPullback = Mapped.isPullback UC.functor-isEquiv
    forward-cone : ConeIso (conePre forward target) mapped
    forward-cone = TargetCone.factor-β mapped
    forward-isEquiv : IsEquiv forward
    forward-isEquiv = pullback-comparison mapped target forward forward-cone mapped-isPullback target-isPullback
```
