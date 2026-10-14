# Changing the normalized separation coordinates

A naturality square in the second coordinate changes both normalized
separation frames by the same output comparison. This retains the
specified product comparisons, including the unchanged first coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.ChangedSeparationFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality 𝒯 M using (productMap-pair-inner)
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedSeparationFrames as Normalized
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp; pair-cong-Iso₂)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (pair-pre-natural-inputs)

module At {X Y A B : CAT} (h : MAP X Y) (f : MAP A B)
  {vY : MAP (Y × A) B} {vX : MAP (X × A) B}
  (θY : (f ∘ pr₂) =₁ vY) (θX : (f ∘ pr₂) =₁ vX)
  (t : (vY ∘ productMap h (id A)) =₁ vX) where
  module N = Normalized.At 𝒯 M h f
  module S = N.S
  σ = N.σ
  HB = N.HB
  δY = pair-cong (comp-unitˡ pr₁) θY
  δX = pair-cong (comp-unitˡ pr₁) θX
  κ = pair-cong (idIso (h ∘ pr₁)) θX
  source-frame = pair-cong N.ρ₁ t ∙ pair-pre pr₁ vY σ
  target-frame = pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ vX) ∙ productMap-pair h (id B) pr₁ vX
  common-source = pair-cong (N.ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ)) (θX ∙ N.source-second) ∙
    pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ
  common-target = pair-cong (h ◁ comp-unitˡ pr₁) (θX ∙ comp-unitˡ (f ∘ pr₂)) ∙
    productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂)

  abstract
    source-old : (κ ∙ S.Source.value) =₂ common-source
    source-old = isoComp-cong (pair-cong-Iso₂ (isoComp-unitˡ-at (N.ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ)))
        (idIso (θX ∙ N.source-second))) (idIso (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ∙
      isoComp-cong ((pair-cong-comp (idIso (h ∘ pr₁)) (N.ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ)) θX N.source-second) ⁻¹)
        (idIso (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ∙
      (isoComp-assoc-at κ (pair-cong (N.ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ)) N.source-second)
        (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ⁻¹ ∙
      isoComp-cong (idIso κ) N.source-expanded

    source-new : (t ∙ (θY ▷ σ)) =₂ (θX ∙ N.source-second) →
      (source-frame ∙ (δY ▷ σ)) =₂ common-source
    source-new square = isoComp-cong (pair-cong-Iso₂ (idIso (N.ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ))) square)
        (idIso (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ∙
      isoComp-cong ((pair-cong-comp N.ρ₁ (comp-unitˡ pr₁ ▷ σ) t (θY ▷ σ)) ⁻¹)
        (idIso (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ∙
      (isoComp-assoc-at (pair-cong N.ρ₁ t) (pair-cong (comp-unitˡ pr₁ ▷ σ) (θY ▷ σ))
        (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ⁻¹ ∙
      isoComp-cong (idIso (pair-cong N.ρ₁ t)) ((pair-pre-natural-inputs (comp-unitˡ pr₁) θY σ) ⁻¹) ∙
      isoComp-assoc-at (pair-cong N.ρ₁ t) (pair-pre pr₁ vY σ) (δY ▷ σ)

    source-value : (t ∙ (θY ▷ σ)) =₂ (θX ∙ N.source-second) →
      (κ ∙ S.Source.value) =₂ (source-frame ∙ (δY ▷ σ))
    source-value square = source-new square ⁻¹ ∙ source-old

    target-old : (κ ∙ S.Target.value) =₂ common-target
    target-old = isoComp-cong (pair-cong-Iso₂ (isoComp-unitˡ-at (h ◁ comp-unitˡ pr₁))
        (idIso (θX ∙ comp-unitˡ (f ∘ pr₂))))
        (idIso (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ∙
      isoComp-cong ((pair-cong-comp (idIso (h ∘ pr₁)) (h ◁ comp-unitˡ pr₁) θX (comp-unitˡ (f ∘ pr₂))) ⁻¹)
        (idIso (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ∙
      (isoComp-assoc-at κ (pair-cong (h ◁ comp-unitˡ pr₁) (comp-unitˡ (f ∘ pr₂)))
        (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ⁻¹ ∙
      isoComp-cong (idIso κ) (N.target-pair ⁻¹)

    target-new : (target-frame ∙ (HB ◁ δX)) =₂ common-target
    target-new = isoComp-cong (pair-cong-Iso₂ (isoComp-unitˡ-at (h ◁ comp-unitˡ pr₁))
        (postWhisker-id-at θX))
        (idIso (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ∙
      isoComp-cong ((pair-cong-comp (idIso (h ∘ pr₁)) (h ◁ comp-unitˡ pr₁)
          (comp-unitˡ vX) (id B ◁ θX)) ⁻¹)
        (idIso (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ∙
      (isoComp-assoc-at (pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ vX))
        (pair-cong (h ◁ comp-unitˡ pr₁) (id B ◁ θX))
        (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ⁻¹ ∙
      isoComp-cong (idIso (pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ vX)))
        (productMap-pair-inner h (id B) (comp-unitˡ pr₁) θX) ∙
      isoComp-assoc-at (pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ vX))
        (productMap-pair h (id B) pr₁ vX) (HB ◁ δX)

    target-value : (κ ∙ S.Target.value) =₂ (target-frame ∙ (HB ◁ δX))
    target-value = target-new ⁻¹ ∙ target-old
```
