# Restriction along the terminal-product inclusion

We retain the comparison `oneProduct-natural` used by decoding. Its
second projection identifies both routes with the restricted functor;
the first projection lands in the terminal category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.UnitRestrictionData
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.DecodingNaturality 𝒯 M using (oneProduct-natural)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
module PS = Projections 𝒯

module Coordinates {A B : CAT} (u : MAP A B) where
  input = oneProduct-in A
  output = oneProduct-in B
  step = productRestriction One u
  head = PS.lift-base u pr₂ input (oneProduct-retraction A)
  endpoint = comp-unitʳ u ∙ head
  base = pair-β₂ (id One ∘ pr₁) (u ∘ pr₂)
  source = PS.compose-base pr₂ step base input endpoint
  target = comp-unitˡ u ∙ project-pair₂ (terminate B) (id B) u
  raw-source = comp-unitʳ u ∙ ((u ◁ oneProduct-retraction A) ∙
    (comp-assoc input pr₂ u ∙ project-pair₂ (id One ∘ pr₁) (u ∘ pr₂) input))
  first : (pr₁ ∘ (step ∘ input)) =₁ (pr₁ ∘ (output ∘ u))
  first = terminal-iso _ _
  second = target ⁻¹ ∙ raw-source
  value = oneProduct-natural u

  abstract
    normalize-source : raw-source =₂ source
    normalize-source = (isoComp-assoc-at (comp-unitʳ u) head
        (project-pair₂ (id One ∘ pr₁) (u ∘ pr₂) input)) ⁻¹ ∙
      isoComp-cong (idIso (comp-unitʳ u))
        ((isoComp-assoc-at (u ◁ oneProduct-retraction A) (comp-assoc input pr₂ u)
          (project-pair₂ (id One ∘ pr₁) (u ∘ pr₂) input)) ⁻¹)

    projection₂ : PS.Square pr₂ source target value
    projection₂ = normalize-source ∙
      (cancel-inverse target raw-source ∙ isoComp-cong (idIso target) (pair-iso-β₂ first second))
```
