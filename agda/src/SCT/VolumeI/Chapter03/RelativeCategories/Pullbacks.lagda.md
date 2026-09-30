# Pullback cospans over a category

The relative pullback has the ordinary pullback of the two underlying
functors as its total category. Choose its structure through the first
projection. The second projection's triangle is determined by the
pullback matching and the given cospan triangles. Consequently that same
matching is an identification over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

abstract
  cancel-right-inverse : {X Y : CAT} {F G H : MAP X Y}
    (β : F =₁ G) (α : F =₁ H) → ((α ∙ β ⁻¹) ∙ β) =₂ α
  cancel-right-inverse β α = isoComp-unitʳ-at α ∙
    (isoComp-cong (idIso α) (isoComp-inverseˡ-at β) ∙ isoComp-assoc-at α (β ⁻¹) β)

module Pullback {C D E S : CAT} {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (u : FunctorOver f h) (v : FunctorOver g h) where
  left-map = FunctorLift.lift u
  right-map = FunctorLift.lift v
  category = Pullbacks.PullbackStructure.Pullback P left-map right-map
  first-map : MAP category C
  first-map = pullback₁
  second-map : MAP category D
  second-map = pullback₂
  projection : MAP category S
  projection = f ∘ first-map
  first : FunctorOver projection f
  first = record { lift = first-map ; comparison = idIso projection }
  first-composite = compose-over u first
  left-triangle = FunctorLift.comparison first-composite
  right-tail = (FunctorLift.comparison v ▷ second-map) ∙
    (comp-assoc second-map right-map h) ⁻¹
  matching : (left-map ∘ first-map) =₁ (right-map ∘ second-map)
  matching = pullbackMatch
  base-matching = h ◁ matching
  right-triangle = (left-triangle ∙ base-matching ⁻¹) ∙ right-tail ⁻¹
  second : FunctorOver projection g
  second = record { lift = second-map ; comparison = right-triangle }
  abstract
    triangle-compatible :
      (FunctorLift.comparison (compose-over v second) ∙ base-matching) =₂ left-triangle
    triangle-compatible = cancel-right-inverse base-matching left-triangle ∙
      isoComp-cong (cancel-right-inverse right-tail (left-triangle ∙ base-matching ⁻¹)) (idIso base-matching)
  match-over : FunctorOverIso (compose-over u first) (compose-over v second)
  match-over = record { underlying = matching ; compatible = triangle-compatible }
```
