# Pullback targets and change of base

The two iterated pullbacks defining the base change of an internal
functor category have the same universal property. Paste each into a
pullback over the original base. The comparison retains the projection
to the new source category, hence is an equivalence over that category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.PullbackTargetsBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P

module Targets {C D S T : CAT} (p : MAP C S) (q : MAP D S) (t : MAP T S) where
  C′ = Pullback p t
  D′ = Pullback q t
  h : MAP C′ C
  h = pullback₁
  p′ : MAP C′ T
  p′ = pullback₂
  q′ : MAP D′ T
  q′ = pullback₂
  f : MAP (Pullback q p) C
  f = pullback₂
  old = Pullback f h
  new = Pullback q′ p′
  old-projection : MAP old C′
  old-projection = pullback₂
  new-projection : MAP new C′
  new-projection = pullback₂

  old-right = coneSwap (pullbackCone q p)
  old-inner = coneSwap (pullbackCone f h)
  old-flat = PasteCones.flatten h p old-right old-inner
  new-right = coneSwap (pullbackCone q t)
  new-inner = coneSwap (pullbackCone q′ p′)
  new-pasted = PasteCones.flatten p′ t new-right new-inner
  change : (t ∘ p′) =₁ (p ∘ h)
  change = (pullbackMatch {f = p} {t}) ⁻¹
  new-flat = changeLeft change new-pasted

  abstract
    old-flat-isPullback : IsPullback old-flat
    old-flat-isPullback = Pasting.paste-isPullback h p q old-right
      (pullback-swap (pullbackCone q p) (pullbackCone-isPullback q p)) old-inner
      (pullback-swap (pullbackCone f h) (pullbackCone-isPullback f h))

    new-flat-isPullback : IsPullback new-flat
    new-flat-isPullback = ChangeLeft.preserve change q new-pasted
      (Pasting.paste-isPullback p′ t q new-right
        (pullback-swap (pullbackCone q t) (pullbackCone-isPullback q t)) new-inner
        (pullback-swap (pullbackCone q′ p′) (pullbackCone-isPullback q′ p′)))

  module Universal = UniversalCone old-flat old-flat-isPullback
  forward : FunctorOver new-projection old-projection
  forward = record { lift = Universal.factor new-flat
    ; comparison = ConeIso.leftIso (Universal.factor-β new-flat) }

  abstract
    forward-isEquiv : IsEquiv (FunctorLift.lift forward)
    forward-isEquiv = pullback-comparison new-flat old-flat (FunctorLift.lift forward)
      (Universal.factor-β new-flat) new-flat-isPullback old-flat-isPullback
```
