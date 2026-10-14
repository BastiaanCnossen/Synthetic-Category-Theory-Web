# Normalized frames for product separation

The two routes defining product separation agree with their normalized
coordinate frames. These equalities identify the chosen comparisons,
including the unitors in the unchanged coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedSeparationFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality 𝒯 M using (productMap-pair-inner)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductCoordinateUnits 𝒯 using (coordinate-inner-unit)
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSeparationProjections as Separation
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductPairingComparisons as Pairs
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp; pair-cong-Iso₂)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (pair-pre-natural-inputs)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (coordinate-left-unit)

module At {X Y A B : CAT} (h : MAP X Y) (f : MAP A B) where
  module S = Separation.Separation 𝒯 M h f
  σ : MAP (X × A) (Y × A)
  σ = S.HA
  HB : MAP (X × B) (Y × B)
  HB = S.HB
  LX = S.LX
  ρ₁ = pair-β₁ (h ∘ pr₁) (id A ∘ pr₂)
  ρ₂ = comp-unitˡ pr₂ ∙ pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)
  source-second = (f ◁ ρ₂) ∙ comp-assoc σ pr₂ f
  δY = pair-cong (comp-unitˡ (pr₁ {Y} {A})) (idIso (f ∘ pr₂ {Y} {A}))
  δX = pair-cong (comp-unitˡ (pr₁ {X} {A})) (idIso (f ∘ pr₂ {X} {A}))
  source-frame = pair-cong ρ₁ source-second ∙ pair-pre pr₁ (f ∘ pr₂) σ
  target-frame = pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ (f ∘ pr₂)) ∙ productMap-pair h (id B) pr₁ (f ∘ pr₂)
  module TargetPair = Pairs.ProductPair 𝒯 M h (id B) (id X ∘ pr₁) (f ∘ pr₂)
    (h ◁ comp-unitˡ pr₁) (comp-unitˡ (f ∘ pr₂))

  abstract
    source-first : S.Source.first =₂ (ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ))
    source-first = coordinate-left-unit pr₁ h pr₁ σ ρ₁

    source-last : S.Source.second =₂ source-second
    source-last = coordinate-inner-unit pr₂ pr₂ σ (pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)) f

    source-expanded : S.Source.value =₂
      (pair-cong (ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ)) source-second ∙ pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)
    source-expanded = isoComp-cong (pair-cong-Iso₂ source-first source-last)
      (idIso (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ∙ S.Source.normalization

    source-frame-expanded : (source-frame ∙ (δY ▷ σ)) =₂
      (pair-cong (ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ)) source-second ∙ pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)
    source-frame-expanded = isoComp-cong (pair-cong-Iso₂ (idIso (ρ₁ ∙ (comp-unitˡ pr₁ ▷ σ)))
        (isoComp-unitʳ-at source-second ∙ isoComp-cong (idIso source-second) (preWhisker-idIso (f ∘ pr₂) σ)))
        (idIso (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ∙
      isoComp-cong ((pair-cong-comp ρ₁ (comp-unitˡ pr₁ ▷ σ) source-second (idIso (f ∘ pr₂) ▷ σ)) ⁻¹)
        (idIso (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ∙
      (isoComp-assoc-at (pair-cong ρ₁ source-second) (pair-cong (comp-unitˡ pr₁ ▷ σ) (idIso (f ∘ pr₂) ▷ σ))
        (pair-pre (id Y ∘ pr₁) (f ∘ pr₂) σ)) ⁻¹ ∙
      isoComp-cong (idIso (pair-cong ρ₁ source-second))
        ((pair-pre-natural-inputs (comp-unitˡ pr₁) (idIso (f ∘ pr₂)) σ) ⁻¹) ∙
      isoComp-assoc-at (pair-cong ρ₁ source-second) (pair-pre pr₁ (f ∘ pr₂) σ) (δY ▷ σ)

    source-value : S.Source.value =₂ (source-frame ∙ (δY ▷ σ))
    source-value = source-frame-expanded ⁻¹ ∙ source-expanded

    target-first : TargetPair.first =₂ S.Target.first
    target-first = (coordinate-inner-unit pr₁ pr₁ LX (pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)) h) ⁻¹ ∙
      isoComp-cong ((postWhisker-isoComp-at h (comp-unitˡ pr₁) (pair-β₁ (id X ∘ pr₁) (f ∘ pr₂))) ⁻¹)
        (idIso (comp-assoc LX pr₁ h)) ∙
      (isoComp-assoc-at (h ◁ comp-unitˡ pr₁) (h ◁ pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)) (comp-assoc LX pr₁ h)) ⁻¹

    target-last : TargetPair.second =₂ S.Target.second
    target-last = (coordinate-left-unit pr₂ f pr₂ LX (pair-β₂ (id X ∘ pr₁) (f ∘ pr₂))) ⁻¹ ∙
      Pairs.identity-coordinate 𝒯 M pr₂ LX (pair-β₂ (id X ∘ pr₁) (f ∘ pr₂))

    target-pair : TargetPair.comparison =₂ S.Target.value
    target-pair = S.Target.normalization ⁻¹ ∙
      isoComp-cong (pair-cong-Iso₂ target-first target-last)
        (idIso (pair-pre (h ∘ pr₁) (id B ∘ pr₂) LX)) ∙ TargetPair.normalization

    target-frame-normal : (target-frame ∙ (HB ◁ δX)) =₂ TargetPair.comparison
    target-frame-normal = isoComp-cong (pair-cong-Iso₂
        (isoComp-unitˡ-at (h ◁ comp-unitˡ pr₁))
        (isoComp-unitʳ-at (comp-unitˡ (f ∘ pr₂)) ∙
          isoComp-cong (idIso (comp-unitˡ (f ∘ pr₂))) (postWhisker-idIso (id B) (f ∘ pr₂))))
        (idIso (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ∙
      isoComp-cong ((pair-cong-comp (idIso (h ∘ pr₁)) (h ◁ comp-unitˡ pr₁)
          (comp-unitˡ (f ∘ pr₂)) (id B ◁ idIso (f ∘ pr₂))) ⁻¹)
        (idIso (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ∙
      (isoComp-assoc-at (pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ (f ∘ pr₂)))
        (pair-cong (h ◁ comp-unitˡ pr₁) (id B ◁ idIso (f ∘ pr₂)))
        (productMap-pair h (id B) (id X ∘ pr₁) (f ∘ pr₂))) ⁻¹ ∙
      isoComp-cong (idIso (pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ (f ∘ pr₂))))
        (productMap-pair-inner h (id B) (comp-unitˡ pr₁) (idIso (f ∘ pr₂))) ∙
      isoComp-assoc-at (pair-cong (idIso (h ∘ pr₁)) (comp-unitˡ (f ∘ pr₂)))
        (productMap-pair h (id B) pr₁ (f ∘ pr₂)) (HB ◁ δX)

    target-value : S.Target.value =₂ (target-frame ∙ (HB ◁ δX))
    target-value = target-frame-normal ⁻¹ ∙ target-pair ⁻¹
```
