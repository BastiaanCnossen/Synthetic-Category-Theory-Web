# Associativity of product substitution

We compare the two iterated substitutions using the existing product
comparison. The pairing calculation below reduces this to its two
coordinate comparisons, preserving the specified external associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSecondCoordinate as ProductSecondCoordinate
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingAssembly as Assembly
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairing as ChosenPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ChosenPairingFunctoriality as ChosenPairingFunctoriality

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateComparisons as CoordinateComparisons

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 using
  (CAT; MAP; id; pr₁; pr₂; _×_; pair; pair-β₁; pair-β₂; pair-cong; pair-pre;
   _∘_; _=₁_; _=₂_; _∙_; _⁻¹; idIso; _◁_; _▷_; comp-assoc;
   productMap; productMap-cong; coordinate-comparison;
   isoComp-cong; isoComp-assoc-at; isoComp-unitˡ-at; isoComp-unitʳ-at;
   isoComp-inverseˡ-at; isoComp-inverseʳ-at; preWhisker; postWhisker;
   preWhisker-isoComp-at; postWhisker-isoComp-at;
   vocabulary; terminal; products; productLaws; composition; vertical;
   whiskering; pentagonTriangle)
open Compatibility 𝒯 M using (slice-comparison)
open ProductSubstitution 𝒯 M using (module Coordinates; coordinate-outer-comp)
open ProductSecondCoordinate 𝒯 M using (second-coordinate-assoc)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs; pair-pre-natural-substitution)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-iterated; pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; postWhisker-comp-at)

private
  module Chosen = ChosenPairing vocabulary terminal products productLaws composition vertical whiskering
    using (operations)
  module ChosenLaws = ChosenPairingFunctoriality vocabulary terminal products productLaws
    composition vertical whiskering pentagonTriangle using (functoriality)
open Assembly vocabulary terminal products productLaws composition vertical whiskering
  Chosen.operations ChosenLaws.functoriality public using (combine-pair; module PairingAssembly)
```

Postcomposition carries a pasted coordinate square to the pasted image
square. The external pentagon accounts for the three reassociations.

```agda
open CoordinateComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle public using (post-pasting; cancel-inverse-tail; cancel-forward)
open CoordinateComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle using (coordinate-at-change)

first-coordinate-assoc : {Q R X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R)
  →
      (Coordinates.first C f (σ ∘ τ) ∙
        (((f ∘ pr₁) ◁ slice-comparison {C = C} σ τ) ∙
          comp-assoc (productMap τ (id C)) (productMap σ (id C)) (f ∘ pr₁))) =₂
      ((comp-assoc τ σ f ▷ pr₁) ∙
        (Coordinates.first C (f ∘ σ) τ ∙
          (Coordinates.first C f σ ▷ productMap τ (id C))))
first-coordinate-assoc C f σ τ =
  let h = productMap σ (id C)
      k = productMap τ (id C)
      l = productMap (σ ∘ τ) (id C)
      κ = slice-comparison {C = C} σ τ
      b = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
      b′ = pair-β₁ ((σ ∘ τ) ∘ pr₁) (id C ∘ pr₂)
      c = Coordinates.first C σ τ
      outside = (comp-assoc pr₁ (σ ∘ τ) f) ⁻¹
      leftImage = f ◁ b′
      inputA = comp-assoc l pr₁ f
      change = (f ∘ pr₁) ◁ κ
      sourceA = comp-assoc k h (f ∘ pr₁)
      normalizeShort = isoComp-cong (idIso outside)
        (coordinate-at-change f pr₁ h k l κ b b′ c (Coordinates.projection₁ C σ τ)) ∙
        isoComp-assoc-at outside (leftImage ∙ inputA) (change ∙ sourceA)
      u = Coordinates.first C f σ
      w = Coordinates.first C (f ∘ σ) τ
      η = comp-assoc τ σ f ▷ pr₁
      sourceCorner = comp-assoc pr₁ σ f
      imageBefore = (f ◁ b) ∙ comp-assoc h pr₁ f
      nextCoordinate = coordinate-comparison pr₁ (σ ∘ τ) (σ ∘ pr₁) k c f
      outerSquare = coordinate-outer-comp pr₁ τ pr₁ k
        (pair-β₁ (τ ∘ pr₁) (id C ∘ pr₂)) σ f
      simplifyCorner = (preWhisker k ◁ cancel-forward sourceCorner imageBefore) ∙
        (preWhisker-isoComp-at sourceCorner u k) ⁻¹
      normalizeLong = isoComp-cong (idIso outside)
        (isoComp-assoc-at (f ◁ c) (comp-assoc k (σ ∘ pr₁) f) (imageBefore ▷ k)) ∙
        (isoComp-assoc-at outside ((f ◁ c) ∙ comp-assoc k (σ ∘ pr₁) f) (imageBefore ▷ k) ∙
          (isoComp-cong (idIso nextCoordinate) simplifyCorner ∙
            (isoComp-assoc-at nextCoordinate (sourceCorner ▷ k) (u ▷ k) ∙
              (isoComp-cong outerSquare (idIso (u ▷ k)) ∙
                (isoComp-assoc-at η w (u ▷ k)) ⁻¹))))
  in normalizeLong ⁻¹ ∙ normalizeShort
```

We now apply the assembly to the two projections of the chosen product
substitution comparison. The normalization witnesses return the conclusion
to `slice-comparison` itself.

```agda
slice-comparison-assoc : {Q R X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R)
  →
      (slice-comparison {C = C} f (σ ∘ τ) ∙
        ((productMap f (id C) ◁ slice-comparison {C = C} σ τ) ∙
          comp-assoc (productMap τ (id C)) (productMap σ (id C)) (productMap f (id C)))) =₂
      (productMap-cong (comp-assoc τ σ f) (idIso (id C)) ∙
        (slice-comparison {C = C} (f ∘ σ) τ ∙
          (slice-comparison {C = C} f σ ▷ productMap τ (id C))))
slice-comparison-assoc C f σ τ =
  let h = productMap σ (id C)
      k = productMap τ (id C)
      l = productMap (σ ∘ τ) (id C)
      κ = slice-comparison {C = C} σ τ
      sourceTail = (productMap f (id C) ◁ κ) ∙ comp-assoc k h (productMap f (id C))
      η = productMap-cong (comp-assoc τ σ f) (idIso (id C))
      normalizeShort = isoComp-cong (Coordinates.normalization C f (σ ∘ τ)) (idIso sourceTail)
      normalizeLong = isoComp-cong (idIso η)
        (isoComp-cong (Coordinates.normalization C (f ∘ σ) τ)
          (preWhisker k ◁ Coordinates.normalization C f σ))
      assembled = PairingAssembly.assemble (f ∘ pr₁) (id C ∘ pr₂) h k l κ
        (Coordinates.first C f σ) (Coordinates.second C f σ)
        (Coordinates.first C (f ∘ σ) τ) (Coordinates.second C (f ∘ σ) τ)
        (Coordinates.first C f (σ ∘ τ)) (Coordinates.second C f (σ ∘ τ))
        (comp-assoc τ σ f ▷ pr₁) (idIso (id C) ▷ pr₂)
        (first-coordinate-assoc C f σ τ) (second-coordinate-assoc C f σ τ)
  in normalizeLong ⁻¹ ∙ (assembled ∙ normalizeShort)
```

