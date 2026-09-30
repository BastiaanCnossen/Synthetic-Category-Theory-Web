# Changing a normalized restriction coordinate

A specified naturality square for the varying coordinate changes the
normalized product restriction comparison. The constant coordinate and
its unitor are retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionComposition as Normalized
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp; pair-cong-Iso₂)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (pair-pre-natural-inputs)

module At {A B C : CAT} (X : CAT) (f : MAP A B) (g : MAP B C)
  {z : MAP (X × B) C} {w : MAP (X × A) C}
  (θ : (g ∘ pr₂) =₁ z) (κ : (g ∘ (f ∘ pr₂)) =₁ w)
  (σ : (z ∘ productMap (id X) f) =₁ w) where
  module N = Normalized.At 𝒯 M X f g
  J = N.J
  change = pair-cong (comp-unitˡ pr₁) θ
  δ = pair-cong (comp-unitˡ pr₁) (κ ∙ comp-assoc pr₂ f g)
  normal = pair-cong N.first σ ∙ pair-pre pr₁ z J
  common = pair-cong (N.first ∙ (comp-unitˡ pr₁ ▷ J)) (κ ∙ N.second) ∙
    pair-pre (id X ∘ pr₁) (g ∘ pr₂) J

  abstract
    right-normal : (δ ∙ productRestriction-comp X f g) =₂ common
    right-normal = isoComp-cong (pair-cong-Iso₂ N.first-comparison
        (isoComp-cong (idIso κ) N.second-comparison ∙
          isoComp-assoc-at κ (comp-assoc pr₂ f g) N.Coordinates.second))
        (idIso (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ∙
      isoComp-cong ((pair-cong-comp (comp-unitˡ pr₁) N.Coordinates.first
          (κ ∙ comp-assoc pr₂ f g) N.Coordinates.second) ⁻¹)
        (idIso (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ∙
      (isoComp-assoc-at δ (pair-cong N.Coordinates.first N.Coordinates.second)
        (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ⁻¹ ∙
      isoComp-cong (idIso δ) N.Coordinates.normalization

    left-normal : (σ ∙ (θ ▷ J)) =₂ (κ ∙ N.second) → (normal ∙ (change ▷ J)) =₂ common
    left-normal square = isoComp-cong (pair-cong-Iso₂ (idIso (N.first ∙ (comp-unitˡ pr₁ ▷ J))) square)
        (idIso (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ∙
      isoComp-cong ((pair-cong-comp N.first (comp-unitˡ pr₁ ▷ J) σ (θ ▷ J)) ⁻¹)
        (idIso (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ∙
      (isoComp-assoc-at (pair-cong N.first σ) (pair-cong (comp-unitˡ pr₁ ▷ J) (θ ▷ J))
        (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ⁻¹ ∙
      isoComp-cong (idIso (pair-cong N.first σ)) ((pair-pre-natural-inputs (comp-unitˡ pr₁) θ J) ⁻¹) ∙
      isoComp-assoc-at (pair-cong N.first σ) (pair-pre pr₁ z J) (change ▷ J)

    value : (σ ∙ (θ ▷ J)) =₂ (κ ∙ N.second) →
      (normal ∙ (change ▷ J)) =₂ (δ ∙ productRestriction-comp X f g)
    value square = right-normal ⁻¹ ∙ left-normal square
```
