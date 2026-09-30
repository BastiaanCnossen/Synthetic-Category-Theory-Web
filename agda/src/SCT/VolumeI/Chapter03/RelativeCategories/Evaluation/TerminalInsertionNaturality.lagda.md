# Naturality of terminal insertion

The specified comparison for inserting a terminal factor is natural in
the functor. Its first projection is the square for the unitors and
projection witnesses; its terminal projection is unique. This is the
other-coordinate version of the earlier decoding restriction calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.TerminalInsertionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.TerminalInsertion 𝒯
  using (module TerminalInsertion)
open TerminalInsertion using (insert-terminal-natural)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-base-outer)
import SCT.VolumeI.Chapter01.Section03.Equivalences as TerminalComparisons
open TerminalComparisons.TerminalTargets vocabulary terminal products productLaws composition
  using (terminal-Iso₂)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pre-square-projection; substitution-square-projection; projected-square)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality; pair-cong-triangle₁)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-id-at; postWhisker-id-at)
module PS = Projections 𝒯

module Coordinates {A B : CAT} (u : MAP A B) where
  input = product-unitʳ-inverse A
  output = product-unitʳ-inverse B
  step = productMap u (id One)
  retraction = pair-β₁ (id A) (terminate A)
  head = PS.lift-base u pr₁ input retraction
  endpoint = comp-unitʳ u ∙ head
  base = pair-β₁ (u ∘ pr₁) (id One ∘ pr₂)
  source = PS.compose-base pr₁ step base input endpoint
  target = comp-unitˡ u ∙ project-pair₁ (id B) (terminate B) u
  raw-source = comp-unitʳ u ∙ ((u ◁ retraction) ∙
    (comp-assoc input pr₁ u ∙ project-pair₁ (u ∘ pr₁) (id One ∘ pr₂) input))
  first = target ⁻¹ ∙ raw-source
  second : (pr₂ ∘ (step ∘ input)) =₁ (pr₂ ∘ (output ∘ u))
  second = terminal-iso _ _
  value = insert-terminal-natural u

  opaque
    normalize-source : raw-source =₂ source
    normalize-source = (isoComp-assoc-at (comp-unitʳ u) head
        (project-pair₁ (u ∘ pr₁) (id One ∘ pr₂) input)) ⁻¹ ∙
      isoComp-cong (idIso (comp-unitʳ u))
        ((isoComp-assoc-at (u ◁ retraction) (comp-assoc input pr₁ u)
          (project-pair₁ (u ∘ pr₁) (id One ∘ pr₂) input)) ⁻¹)

    projection₁ : PS.Square pr₁ source target value
    projection₁ = normalize-source ∙
      (cancel-inverse target raw-source ∙ isoComp-cong (idIso target) (pair-iso-β₁ first second))

module Naturality {A B : CAT} {u v : MAP A B} (α : u =₁ v) where
  module U = Coordinates u
  module V = Coordinates v
  IA = product-unitʳ-inverse A
  IB = product-unitʳ-inverse B
  δ = productMap-cong α (idIso (id One))
  source-action = δ ▷ IA
  target-action = IB ◁ α
  ru = transport-pre pr₁ U.step U.base IA
  rv = transport-pre pr₁ V.step V.base IA
  tu = transport-pre pr₁ IB (pair-β₁ (id B) (terminate B)) u
  tv = transport-pre pr₁ IB (pair-β₁ (id B) (terminate B)) v

  opaque
    head-square : (V.endpoint ∙ ((α ▷ pr₁) ▷ IA)) =₂ (α ∙ U.endpoint)
    head-square = paste-squares U.head V.head (comp-unitʳ u) (comp-unitʳ v)
      ((α ▷ pr₁) ▷ IA) (α ▷ id A) α
      (lift-base-outer pr₁ (id A) IA (pair-β₁ (id A) (terminate A)) α) (preWhisker-id-at α)

    source-change : (V.source ∙ (pr₁ ◁ source-action)) =₂ (α ∙ U.source)
    source-change = paste-squares ru rv U.endpoint V.endpoint
      (pr₁ ◁ source-action) ((α ▷ pr₁) ▷ IA) α
      (pre-square-projection pr₁ δ (α ▷ pr₁) U.base V.base IA
        (pair-cong-triangle₁ (α ▷ pr₁) (idIso (id One) ▷ pr₂))) head-square

    target-change : (V.target ∙ (pr₁ ◁ target-action)) =₂ (α ∙ U.target)
    target-change = paste-squares tu tv (comp-unitˡ u) (comp-unitˡ v)
      (pr₁ ◁ target-action) (id B ◁ α) α
      (substitution-square-projection pr₁ IB (id B) (pair-β₁ (id B) (terminate B)) α)
      (postWhisker-id-at α)

    first : (pr₁ ◁ (V.value ∙ source-action)) =₂ (pr₁ ◁ (target-action ∙ U.value))
    first = (projected-square pr₁ target-action U.value V.value source-action
      U.target V.target α U.source V.source
      target-change U.projection₁ V.projection₁ source-change) ⁻¹

    comparison : (V.value ∙ source-action) =₂ (target-action ∙ U.value)
    comparison = pair-iso-extensionality first (terminal-Iso₂ _ _)
```
