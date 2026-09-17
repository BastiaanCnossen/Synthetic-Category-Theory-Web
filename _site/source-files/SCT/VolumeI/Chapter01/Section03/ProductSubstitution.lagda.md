# Product substitution and its projections

The uncurrying substitution comparison uses the chosen composition
comparison for `f × id C`. We expose its two projection witnesses here.
These concern that existing comparison, including its unit normalization.
They are preparatory lemmas for its associativity coherence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.CoherenceTransport as CoherenceTransport

module SCT.VolumeI.Chapter01.Section03.ProductSubstitution
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

  first : =₁ ((f ∘ pr₁) ∘ substitution) ((f ∘ σ) ∘ pr₁)
  first = invIso (comp-assoc pr₁ σ f) ∙
    ((f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc substitution pr₁ f)

  secondBeforeUnit : =₁ ((id C ∘ pr₂) ∘ substitution) ((id C ∘ id C) ∘ pr₂)
  secondBeforeUnit = invIso (comp-assoc pr₂ (id C) (id C)) ∙
    ((id C ◁ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc substitution pr₂ (id C))

  second : =₁ ((id C ∘ pr₂) ∘ substitution) (id C ∘ pr₂)
  second = (comp-unitˡ (id C) ▷ pr₂) ∙ secondBeforeUnit

  normalized : =₁ (productMap f (id C) ∘ substitution) (productMap (f ∘ σ) (id C))
  normalized = pair-cong first second ∙ pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution

  normalization : =₂ (slice-comparison {C = C} f σ) normalized
  normalization =
    let firstUnit = idIso (f ∘ σ) ▷ pr₁
        secondUnit = comp-unitˡ (id C) ▷ pr₂
        firstNormalization = isoComp-unitˡ-at first ∙
          isoComp-cong (preWhisker-idIso (f ∘ σ) pr₁) (idIso first)
        pairedNormalization = pair-cong-Iso₂ firstNormalization (idIso second) ∙
          invIso (pair-cong-comp firstUnit first secondUnit secondBeforeUnit)
    in isoComp-cong pairedNormalization
        (idIso (pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution)) ∙
      invIso (isoComp-assoc-at (pair-cong firstUnit secondUnit)
        (pair-cong first secondBeforeUnit) (pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution))

  projection₁ : =₂
    (pair-β₁ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂) ∙ (pr₁ ◁ slice-comparison {C = C} f σ))
    (first ∙ ((pair-β₁ (f ∘ pr₁) (id C ∘ pr₂) ▷ substitution) ∙
      invIso (comp-assoc substitution (productMap f (id C)) pr₁)))
  projection₁ = pair-pre-cong-triangle₁ (f ∘ pr₁) (id C ∘ pr₂) substitution first second ∙
    isoComp-cong (idIso (pair-β₁ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂)))
      (postWhisker pr₁ ◁ normalization)

  projection₂ : =₂
    (pair-β₂ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂) ∙ (pr₂ ◁ slice-comparison {C = C} f σ))
    (second ∙ ((pair-β₂ (f ∘ pr₁) (id C ∘ pr₂) ▷ substitution) ∙
      invIso (comp-assoc substitution (productMap f (id C)) pr₂)))
  projection₂ = pair-pre-cong-triangle₂ (f ∘ pr₁) (id C ∘ pr₂) substitution first second ∙
    isoComp-cong (idIso (pair-β₂ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂)))
      (postWhisker pr₂ ◁ normalization)
```

The next lemma checks successive postcomposition of a coordinate
comparison. Its three squares are, in order, the primitive pentagon,
naturality of the primitive associator, and a rearrangement of another
primitive pentagon. Naming these squares keeps the argument visible.

```agda
private
  post-inverse : {X C D : CAT} (F : MAP C D) {u v : MAP X C} (α : =₁ u v)
    → =₂ (F ◁ invIso α) (invIso (F ◁ α))
  post-inverse F {u} α = cancel-right-reflect (F ◁ α)
    (invIso (isoComp-inverseˡ-at (F ◁ α)) ∙
    (postWhisker-idIso F u ∙
    ((postWhisker F ◁ isoComp-inverseˡ-at α) ∙
      invIso (postWhisker-isoComp-at F (invIso α) α))))

coordinate-outer-comp : {R X K C D E : CAT}
  (ρ : MAP R X) (s : MAP X C) (π : MAP K C) (h : MAP R K)
  (b : =₁ (π ∘ h) (s ∘ ρ)) (g : MAP C D) (f : MAP D E)
  → =₂
      ((comp-assoc s g f ▷ ρ) ∙ coordinate-comparison ρ s π h b (f ∘ g))
      (coordinate-comparison ρ (g ∘ s) (g ∘ π) h
        (coordinate-comparison ρ s π h b g) f ∙ (comp-assoc π g f ▷ h))
coordinate-outer-comp ρ s π h b g f =
  let inputLeft = comp-assoc h π (f ∘ g)
      middleLeft = (f ∘ g) ◁ b
      outputLeft = invIso (comp-assoc ρ s (f ∘ g))
      inputRight = (f ◁ comp-assoc h π g) ∙ comp-assoc h (g ∘ π) f
      middleRight = f ◁ (g ◁ b)
      outputRight = invIso (comp-assoc ρ (g ∘ s) f) ∙ (f ◁ invIso (comp-assoc ρ s g))
      atSource = comp-assoc π g f ▷ h
      afterInput = comp-assoc (π ∘ h) g f
      beforeOutput = comp-assoc (s ∘ ρ) g f
      atTarget = comp-assoc s g f ▷ ρ

      inputSquare : =₂ (inputRight ∙ atSource) (afterInput ∙ inputLeft)
      inputSquare = invIso (pentagon-whiskered h π g f) ∙
        isoComp-assoc-at (f ◁ comp-assoc h π g) (comp-assoc h (g ∘ π) f) atSource

      middleSquare : =₂ (middleRight ∙ afterInput) (beforeOutput ∙ middleLeft)
      middleSquare = invIso (postWhisker-comp-at b g f)

      outputSquare : =₂ (outputRight ∙ beforeOutput) (atTarget ∙ outputLeft)
      outputSquare = pentagon-left-corner beforeOutput (comp-assoc ρ s (f ∘ g))
          (f ◁ comp-assoc ρ s g) (comp-assoc ρ (g ∘ s) f) atTarget
          (pentagon-whiskered ρ s g f) ∙
        (isoComp-assoc-at (invIso (comp-assoc ρ (g ∘ s) f))
          (invIso (f ◁ comp-assoc ρ s g)) beforeOutput ∙
        isoComp-cong
          (isoComp-cong (idIso (invIso (comp-assoc ρ (g ∘ s) f))) (post-inverse f (comp-assoc ρ s g)))
          (idIso beforeOutput))

      assembled : =₂ ((outputRight ∙ (middleRight ∙ inputRight)) ∙ atSource)
        (atTarget ∙ (outputLeft ∙ (middleLeft ∙ inputLeft)))
      assembled = paste-squares (middleLeft ∙ inputLeft) (middleRight ∙ inputRight)
        outputLeft outputRight atSource beforeOutput atTarget
        (paste-squares inputLeft inputRight middleLeft middleRight
          atSource afterInput beforeOutput inputSquare middleSquare) outputSquare

      outside = invIso (comp-assoc ρ (g ∘ s) f)
      firstImage = f ◁ invIso (comp-assoc ρ s g)
      lastImage = f ◁ comp-assoc h π g
      finalInput = comp-assoc h (g ∘ π) f
      mergeImages : =₂ (firstImage ∙ (middleRight ∙ lastImage))
        (f ◁ coordinate-comparison ρ s π h b g)
      mergeImages = invIso (postWhisker-isoComp-at f (invIso (comp-assoc ρ s g))
          ((g ◁ b) ∙ comp-assoc h π g)) ∙
        isoComp-cong (idIso firstImage) (invIso (postWhisker-isoComp-at f (g ◁ b) (comp-assoc h π g)))

      normalizeRight : =₂ (outputRight ∙ (middleRight ∙ inputRight))
        (coordinate-comparison ρ (g ∘ s) (g ∘ π) h (coordinate-comparison ρ s π h b g) f)
      normalizeRight = isoComp-cong (idIso outside)
        (isoComp-cong mergeImages (idIso finalInput) ∙
        (invIso (isoComp-assoc-at firstImage (middleRight ∙ lastImage) finalInput) ∙
          isoComp-cong (idIso firstImage) (invIso (isoComp-assoc-at middleRight lastImage finalInput)))) ∙
        isoComp-assoc-at outside firstImage (middleRight ∙ (lastImage ∙ finalInput))
  in isoComp-cong normalizeRight (idIso atSource) ∙ invIso assembled
```
