# Decoding respects isomorphisms of restrictions

The terminal-product comparison is natural in the restricted functor.
Its terminal coordinate is unique; its other coordinate is the naturality
square for the unitors and the specified projection witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.UnitRestrictionData as Unit
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.UnitRestrictionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-base-outer)
open import SCT.VolumeI.Chapter01.Section04.Substitution.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pre-square-projection; substitution-square-projection; projected-square)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality; pair-cong-triangle₂)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-id-at; postWhisker-id-at)

module Naturality {A B : CAT} {u v : MAP A B} (α : u =₁ v) where
  module U = Unit.Coordinates 𝒯 M u
  module V = Unit.Coordinates 𝒯 M v
  IA = oneProduct-in A
  IB = oneProduct-in B
  δ = productMap-cong (idIso (id One)) α
  source-action = δ ▷ IA
  target-action = IB ◁ α
  ru = transport-pre pr₂ U.step U.base IA
  rv = transport-pre pr₂ V.step V.base IA
  tu = transport-pre pr₂ IB (oneProduct-retraction B) u
  tv = transport-pre pr₂ IB (oneProduct-retraction B) v

  abstract
    head-square : (V.endpoint ∙ ((α ▷ pr₂) ▷ IA)) =₂ (α ∙ U.endpoint)
    head-square = paste-squares U.head V.head (comp-unitʳ u) (comp-unitʳ v)
      ((α ▷ pr₂) ▷ IA) (α ▷ id A) α
      (lift-base-outer pr₂ (id A) IA (oneProduct-retraction A) α) (preWhisker-id-at α)

    source-change : (V.source ∙ (pr₂ ◁ source-action)) =₂ (α ∙ U.source)
    source-change = paste-squares ru rv U.endpoint V.endpoint
      (pr₂ ◁ source-action) ((α ▷ pr₂) ▷ IA) α
      (pre-square-projection pr₂ δ (α ▷ pr₂) U.base V.base IA
        (pair-cong-triangle₂ (idIso (id One) ▷ pr₁) (α ▷ pr₂))) head-square

    target-change : (V.target ∙ (pr₂ ◁ target-action)) =₂ (α ∙ U.target)
    target-change = paste-squares tu tv (comp-unitˡ u) (comp-unitˡ v)
      (pr₂ ◁ target-action) (id B ◁ α) α
      (substitution-square-projection pr₂ IB (id B) (oneProduct-retraction B) α)
      (postWhisker-id-at α)

    second : (pr₂ ◁ (V.value ∙ source-action)) =₂ (pr₂ ◁ (target-action ∙ U.value))
    second = (projected-square pr₂ target-action U.value V.value source-action
      U.target V.target α U.source V.source
      target-change U.projection₂ V.projection₂ source-change) ⁻¹

    comparison : (V.value ∙ source-action) =₂ (target-action ∙ U.value)
    comparison = pair-iso-extensionality (terminal-Iso₂ _ _) second
```
