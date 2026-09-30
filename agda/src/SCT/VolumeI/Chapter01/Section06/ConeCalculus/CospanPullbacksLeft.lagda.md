# Pullback transport with a cartesian left square

This is the symmetric form of `CospanPullbacks`. The explicit reversal
comparison ensures that the result is about the original mapped cone,
with its original matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacksLeft
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; IsPullback; pullback-cone-invariant; pullback-comparison)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneIso-swap; coneSwap-pre; coneIso-inverse; coneIso-compose; coneSwap-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as Right
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanSymmetry as Symmetry

leftSquareOf : {C D E C′ D′ E′ : CAT} {f : MAP C E} {g : MAP D E}
  {f′ : MAP C′ E′} {g′ : MAP D′ E′} (F : CospanMap f g f′ g′) →
  Cone f′ (CospanMap.base F) C
leftSquareOf F = record
  { left = CospanMap.left F ; right = _ ; match = CospanMap.leftSquare F }

module Mapped {C D E C′ D′ E′ X : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (left-pullback : IsPullback (leftSquareOf F))
  (source : Cone f g X) (source-isPullback : IsPullback source) where
  private
    module Reversed = Right.Mapped 𝒯 P (Symmetry.swap-cospan 𝒯 P F) left-pullback
      (coneSwap source) (pullback-swap source source-isPullback) using (isPullback)
    module Reversal = Symmetry.At 𝒯 P F source using (comparison)

  abstract
    isPullback : IsEquiv (CospanMap.right F) → IsPullback (CospanMap.mapCone F source)
    isPullback e = pullback-cone-invariant (coneSwap-swap (CospanMap.mapCone F source))
      (pullback-swap (coneSwap (CospanMap.mapCone F source))
        (pullback-cone-invariant (coneIso-inverse Reversal.comparison) (Reversed.isPullback e)))

  module Specified {Y : CAT} (target : Cone f′ g′ Y) (et : IsPullback target)
    (h : MAP X Y) (θ : ConeIso (conePre h target) (CospanMap.mapCone F source)) where
    abstract
      comparison-isEquiv : IsEquiv (CospanMap.right F) → IsEquiv h
      comparison-isEquiv e = pullback-comparison (CospanMap.mapCone F source) target h θ (isPullback e) et
```


The same cartesian left face gives a pullback square on the right
projections for any specified source and target pullbacks. No equivalence
of the right cospan map is needed for this assertion.

```agda
module ProjectionSquare {C D E C′ D′ E′ X Y : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (left-pullback : IsPullback (leftSquareOf F))
  (source : Cone f g X) (source-isPullback : IsPullback source)
  (target : Cone f′ g′ Y) (target-isPullback : IsPullback target)
  (h : MAP X Y) (Φ : ConeIso (conePre h target) (CospanMap.mapCone F source)) where
  private
    module Reversal = Symmetry.At 𝒯 P F source using (comparison)
    reversed-comparison : ConeIso (conePre h (coneSwap target))
      (CospanMap.mapCone (Symmetry.swap-cospan 𝒯 P F) (coneSwap source))
    reversed-comparison = coneIso-compose Reversal.comparison
      (coneIso-compose (coneIso-swap Φ) (coneSwap-pre h target))
    module Result = Right.Specified 𝒯 P (Symmetry.swap-cospan 𝒯 P F) left-pullback
      (coneSwap source) (pullback-swap source source-isPullback)
      (coneSwap target) (pullback-swap target target-isPullback)
      h reversed-comparison using (projectionSquare; projection-square-isPullback)
  square = Result.projectionSquare
  abstract
    square-isPullback : IsPullback square
    square-isPullback = Result.projection-square-isPullback
```
