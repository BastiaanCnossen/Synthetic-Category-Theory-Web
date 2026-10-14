# Product substitution and its projections

The uncurrying substitution comparison uses the chosen composition
comparison for `f × id C`. We expose its two projection witnesses here.
These concern that existing comparison, including its unit normalization.
They are preparatory lemmas for its associativity coherence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport as CoherenceTransport

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateComparisons as CoordinateComparisons

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Compatibility 𝒯 M using (slice-comparison)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)
open CoherenceTransport 𝒯 using (pentagon-left-corner)

module Coordinates {Y X Z : CAT} (C : CAT) (f : MAP X Z) (σ : MAP Y X) where
  substitution : MAP (Y × C) (X × C)
  substitution = productMap σ (id C)

  first : ((f ∘ pr₁) ∘ substitution) =₁ ((f ∘ σ) ∘ pr₁)
  first = (comp-assoc pr₁ σ f) ⁻¹ ∙
    ((f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc substitution pr₁ f)

  secondBeforeUnit : ((id C ∘ pr₂) ∘ substitution) =₁ ((id C ∘ id C) ∘ pr₂)
  secondBeforeUnit = (comp-assoc pr₂ (id C) (id C)) ⁻¹ ∙
    ((id C ◁ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc substitution pr₂ (id C))

  second : ((id C ∘ pr₂) ∘ substitution) =₁ (id C ∘ pr₂)
  second = (comp-unitˡ (id C) ▷ pr₂) ∙ secondBeforeUnit

  normalized : (productMap f (id C) ∘ substitution) =₁ (productMap (f ∘ σ) (id C))
  normalized = pair-cong first second ∙ pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution

  normalization : (slice-comparison {C = C} f σ) =₂ normalized
  normalization =
    let firstUnit = idIso (f ∘ σ) ▷ pr₁
        secondUnit = comp-unitˡ (id C) ▷ pr₂
        firstNormalization = isoComp-unitˡ-at first ∙
          isoComp-cong (preWhisker-idIso (f ∘ σ) pr₁) (idIso first)
        pairedNormalization = pair-cong-Iso₂ firstNormalization (idIso second) ∙
          (pair-cong-comp firstUnit first secondUnit secondBeforeUnit) ⁻¹
    in isoComp-cong pairedNormalization
        (idIso (pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution)) ∙
      (isoComp-assoc-at (pair-cong firstUnit secondUnit)
        (pair-cong first secondBeforeUnit) (pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution)) ⁻¹

  projection₁ :
    (pair-β₁ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂) ∙ (pr₁ ◁ slice-comparison {C = C} f σ)) =₂
    (first ∙ ((pair-β₁ (f ∘ pr₁) (id C ∘ pr₂) ▷ substitution) ∙
      (comp-assoc substitution (productMap f (id C)) pr₁) ⁻¹))
  projection₁ = pair-pre-cong-triangle₁ (f ∘ pr₁) (id C ∘ pr₂) substitution first second ∙
    isoComp-cong (idIso (pair-β₁ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂)))
      (postWhisker pr₁ ◁ normalization)

  projection₂ :
    (pair-β₂ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂) ∙ (pr₂ ◁ slice-comparison {C = C} f σ)) =₂
    (second ∙ ((pair-β₂ (f ∘ pr₁) (id C ∘ pr₂) ▷ substitution) ∙
      (comp-assoc substitution (productMap f (id C)) pr₂) ⁻¹))
  projection₂ = pair-pre-cong-triangle₂ (f ∘ pr₁) (id C ∘ pr₂) substitution first second ∙
    isoComp-cong (idIso (pair-β₂ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂)))
      (postWhisker pr₂ ◁ normalization)
```

Successive postcomposition of a coordinate comparison is treated in
`IdentificationCalculus.CoordinateComparisons`. Its three squares are the
primitive pentagon, naturality of the primitive associator, and a
rearrangement of another primitive pentagon. We use that calculation here.

```agda
open CoordinateComparisons vocabulary terminal products productLaws composition vertical whiskering
  pentagonTriangle public using (coordinate-outer-comp)

```
