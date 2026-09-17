# Decoding respects isomorphisms of restrictions

The terminal-product comparison is natural in the restricted functor.
Its terminal coordinate is unique; its other coordinate is the naturality
square for the unitors and the specified projection witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.UnitRestrictionData as Unit
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.UnitRestrictionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯 using (lift-base-outer)
open import SCT.VolumeI.Chapter01.Section03.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pre-square-projection; substitution-square-projection; projected-square)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality; pair-cong-triangle₂)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-id-at; postWhisker-id-at)

module Naturality {A B : CAT} {u v : MAP A B} (α : NatIso u v) where
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
    head-square : Iso₂ (V.endpoint ∙ ((α ▷ pr₂) ▷ IA)) (α ∙ U.endpoint)
    head-square = paste-squares U.head V.head (comp-unitʳ u) (comp-unitʳ v)
      ((α ▷ pr₂) ▷ IA) (α ▷ id A) α
      (lift-base-outer pr₂ (id A) IA (oneProduct-retraction A) α) (preWhisker-id-at α)

    source-change : Iso₂ (V.source ∙ (pr₂ ◁ source-action)) (α ∙ U.source)
    source-change = paste-squares ru rv U.endpoint V.endpoint
      (pr₂ ◁ source-action) ((α ▷ pr₂) ▷ IA) α
      (pre-square-projection pr₂ δ (α ▷ pr₂) U.base V.base IA
        (pair-cong-triangle₂ (idIso (id One) ▷ pr₁) (α ▷ pr₂))) head-square

    target-change : Iso₂ (V.target ∙ (pr₂ ◁ target-action)) (α ∙ U.target)
    target-change = paste-squares tu tv (comp-unitˡ u) (comp-unitˡ v)
      (pr₂ ◁ target-action) (id B ◁ α) α
      (substitution-square-projection pr₂ IB (id B) (oneProduct-retraction B) α)
      (postWhisker-id-at α)

    second : Iso₂ (pr₂ ◁ (V.value ∙ source-action)) (pr₂ ◁ (target-action ∙ U.value))
    second = invIso (projected-square pr₂ target-action U.value V.value source-action
      U.target V.target α U.source V.source
      target-change U.projection₂ V.projection₂ source-change)

    comparison : Iso₂ (V.value ∙ source-action) (target-action ∙ U.value)
    comparison = pair-iso-extensionality (terminal-Iso₂ _ _) second
```
