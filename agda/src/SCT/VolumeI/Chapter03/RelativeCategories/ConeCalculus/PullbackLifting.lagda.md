# Lifting a cone over the base

Lift its underlying cone into the absolute pullback. The first
projection determines the lift's base triangle. Its first beta
comparison respects that triangle; the matching of the full pullback
beta cone then proves the same for the second comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeComparisons 𝒯 M ℱ P using (module RightLeg)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Lift {X C D E S : CAT} {t : MAP X S} {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (u : FunctorOver f h) (v : FunctorOver g h)
  (x : FunctorOver t f) (y : FunctorOver t g)
  (matching : FunctorOverIso (compose-over u x) (compose-over v y)) where
  module PB = RelativePullback u v
  cone : Cone (FunctorLift.lift u) (FunctorLift.lift v) X
  cone = record { left = FunctorLift.lift x ; right = FunctorLift.lift y
    ; match = FunctorOverIso.underlying matching }
  functor : MAP X PB.category
  functor = pullbackLift cone
  β₁ = pullbackLift-β₁ cone
  β₂ = pullbackLift-β₂ cone
  assoc = comp-assoc functor PB.first-map f
  triangle = FunctorLift.comparison x ∙ ((f ◁ β₁) ∙ assoc)
  over : FunctorOver t PB.projection
  over = record { lift = functor ; comparison = triangle }

  abstract
    first-triangle : FunctorLift.comparison (compose-over PB.first over) =₂
      (FunctorLift.comparison x ∙ (f ◁ β₁))
    first-triangle = cancel-right assoc (FunctorLift.comparison x ∙ (f ◁ β₁)) ∙
      (isoComp-cong ((isoComp-assoc-at (FunctorLift.comparison x) (f ◁ β₁) assoc) ⁻¹) (idIso (assoc ⁻¹)) ∙
        isoComp-cong (idIso triangle)
          (isoComp-unitˡ-at (assoc ⁻¹) ∙
            isoComp-cong (preWhisker-idIso PB.projection functor) (idIso (assoc ⁻¹))))
    first-comparison : FunctorOverIso (compose-over PB.first over) x
    first-comparison = record { underlying = β₁ ; compatible = first-triangle ⁻¹ }

  restricted-match : FunctorOverIso
    (compose-over u (compose-over PB.first over))
    (compose-over v (compose-over PB.second over))
  restricted-match = compose-iso-over (associator-over over PB.second v)
    (compose-iso-over (prewhisker-over over PB.match-over)
      (inverse-iso-over (associator-over over PB.first u)))

  abstract
    second-comparison : FunctorOverIso (compose-over PB.second over) y
    second-comparison = RightLeg.comparison u v (compose-over PB.first over) x
      (compose-over PB.second over) y restricted-match matching first-comparison β₂
      (ConeIso.compatible (pullbackLift-β cone))

    cone-comparison : ConeIso (conePre functor (pullbackCone (FunctorLift.lift u) (FunctorLift.lift v))) cone
    cone-comparison = pullbackLift-β cone
```
