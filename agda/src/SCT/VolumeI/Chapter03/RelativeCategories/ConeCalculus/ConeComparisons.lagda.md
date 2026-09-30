# Recovering the second leg of a relative cone comparison

Once the first leg respects the base, compatibility with the two cone
matchings forces the second leg to respect it as well. Cancel the
specified base triangle of the second cospan arrow. No faithfulness of
that arrow is needed, since its prescribed image is already given.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionReflection 𝒯 M ℱ P using (module Recover)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module RightLeg {X C D E S : CAT} {t : MAP X S} {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (u : FunctorOver f h) (v : FunctorOver g h)
  (x₁ y₁ : FunctorOver t f) (x₂ y₂ : FunctorOver t g)
  (source : FunctorOverIso (compose-over u x₁) (compose-over v x₂))
  (target : FunctorOverIso (compose-over u y₁) (compose-over v y₂))
  (left : FunctorOverIso x₁ y₁) (right : FunctorLift.lift x₂ =₁ FunctorLift.lift y₂)
  (square : (FunctorOverIso.underlying target ∙ (FunctorLift.lift u ◁ FunctorOverIso.underlying left)) =₂
    ((FunctorLift.lift v ◁ right) ∙ FunctorOverIso.underlying source)) where
  source-match = FunctorOverIso.underlying source
  target-match = FunctorOverIso.underlying target
  left-image = FunctorLift.lift u ◁ FunctorOverIso.underlying left
  right-image = FunctorLift.lift v ◁ right
  comparison-after-v : FunctorOverIso (compose-over v x₂) (compose-over v y₂)
  comparison-after-v = compose-iso-over target
    (compose-iso-over (postwhisker-over u left) (inverse-iso-over source))
  abstract
    image : right-image =₂ FunctorOverIso.underlying comparison-after-v
    image = isoComp-assoc-at target-match left-image (source-match ⁻¹) ∙
      (isoComp-cong (square ⁻¹) (idIso (source-match ⁻¹)) ∙
        (cancel-right source-match right-image) ⁻¹)
    comparison : FunctorOverIso x₂ y₂
    comparison = Recover.comparison v comparison-after-v right image
```
