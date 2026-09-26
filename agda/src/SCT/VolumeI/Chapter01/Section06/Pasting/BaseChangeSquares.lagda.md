# Composing base-change squares

The outer rectangle of two pullback squares is again a pullback.
This is the existing pasting theorem, oriented for successive changes
of base in the definition of exponentiability.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)

module Successive {S T S′ T′ S″ T″ : CAT} (p : MAP S T) (b : MAP T′ T)
  (first : Cone p b S′) (b′ : MAP T″ T′) (second : Cone (Cone.right first) b′ S″) where

  composite : Cone p (b ∘ b′) S″
  composite = coneSwap (PasteCones.flatten b′ b (coneSwap first) (coneSwap second))

  abstract
    composite-isPullback : IsPullback first → IsPullback second → IsPullback composite
    composite-isPullback e₁ e₂ = pullback-swap _
      (Pasting.paste-isPullback b′ b p (coneSwap first) (pullback-swap first e₁)
        (coneSwap second) (pullback-swap second e₂))
```
