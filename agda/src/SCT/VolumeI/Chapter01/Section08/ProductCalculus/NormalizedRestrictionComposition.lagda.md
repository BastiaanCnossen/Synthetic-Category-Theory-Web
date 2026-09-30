# Normalizing restriction composition

The product restriction compositor agrees with substitution in normalized
coordinates. The comparison retains the unitor of the constant coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductRestrictionAssociativity as Restriction
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp; pair-cong-Iso₂)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (pair-pre-natural-inputs)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {A B C : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) where
  J : MAP (X × A) (X × B)
  J = productMap (id X) f
  module Coordinates = Restriction.Coordinates 𝒯 M X g f
  β₁ : (pr₁ ∘ J) =₁ (id X ∘ pr₁)
  β₁ = pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)
  β₂ : (pr₂ ∘ J) =₁ (f ∘ pr₂)
  β₂ = pair-β₂ (id X ∘ pr₁) (f ∘ pr₂)
  first : (pr₁ ∘ J) =₁ (pr₁ {X} {A})
  first = comp-unitˡ pr₁ ∙ β₁
  second : ((g ∘ pr₂) ∘ J) =₁ (g ∘ (f ∘ pr₂))
  second = (g ◁ β₂) ∙ comp-assoc J pr₂ g
  δ : productMap (id X) (g ∘ f) =₁ pair (pr₁ {X} {A}) (g ∘ (f ∘ pr₂))
  δ = pair-cong (comp-unitˡ pr₁) (comp-assoc pr₂ f g)
  outer : productMap (id X) g =₁ pair (pr₁ {X} {B}) (g ∘ pr₂)
  outer = pair-cong (comp-unitˡ pr₁) (idIso (g ∘ pr₂))
  normalized : (pair (pr₁ {X} {B}) (g ∘ pr₂) ∘ J) =₁ pair (pr₁ {X} {A}) (g ∘ (f ∘ pr₂))
  normalized = pair-cong first second ∙ pair-pre pr₁ (g ∘ pr₂) J

  abstract
    first-comparison : (comp-unitˡ pr₁ ∙ Coordinates.first) =₂ (first ∙ (comp-unitˡ pr₁ ▷ J))
    first-comparison = (isoComp-assoc-at (comp-unitˡ pr₁) β₁ (comp-unitˡ pr₁ ▷ J)) ⁻¹ ∙
      isoComp-cong (idIso (comp-unitˡ pr₁)) (Restriction.constant-normalization 𝒯 M X g f)

    second-comparison : (comp-assoc pr₂ f g ∙ Coordinates.second) =₂ second
    second-comparison = cancel-inverse (comp-assoc pr₂ f g) second

    expanded : (δ ∙ productRestriction-comp X f g) =₂
      (pair-cong (first ∙ (comp-unitˡ pr₁ ▷ J)) second ∙ pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)
    expanded = isoComp-cong (pair-cong-Iso₂ first-comparison second-comparison)
        (idIso (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ∙
      isoComp-cong ((pair-cong-comp (comp-unitˡ pr₁) Coordinates.first (comp-assoc pr₂ f g) Coordinates.second) ⁻¹)
        (idIso (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ∙
      (isoComp-assoc-at δ (pair-cong Coordinates.first Coordinates.second)
        (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ⁻¹ ∙
      isoComp-cong (idIso δ) Coordinates.normalization

    normal-form : (normalized ∙ (outer ▷ J)) =₂
      (pair-cong (first ∙ (comp-unitˡ pr₁ ▷ J)) second ∙ pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)
    normal-form = isoComp-cong (pair-cong-Iso₂ (idIso (first ∙ (comp-unitˡ pr₁ ▷ J)))
        (isoComp-unitʳ-at second ∙ isoComp-cong (idIso second) (preWhisker-idIso (g ∘ pr₂) J)))
        (idIso (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ∙
      isoComp-cong ((pair-cong-comp first (comp-unitˡ pr₁ ▷ J) second (idIso (g ∘ pr₂) ▷ J)) ⁻¹)
        (idIso (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ∙
      (isoComp-assoc-at (pair-cong first second)
        (pair-cong (comp-unitˡ pr₁ ▷ J) (idIso (g ∘ pr₂) ▷ J))
        (pair-pre (id X ∘ pr₁) (g ∘ pr₂) J)) ⁻¹ ∙
      isoComp-cong (idIso (pair-cong first second))
        ((pair-pre-natural-inputs (comp-unitˡ pr₁) (idIso (g ∘ pr₂)) J) ⁻¹) ∙
      isoComp-assoc-at (pair-cong first second) (pair-pre pr₁ (g ∘ pr₂) J) (outer ▷ J)

    value : (normalized ∙ (outer ▷ J)) =₂ (δ ∙ productRestriction-comp X f g)
    value = expanded ⁻¹ ∙ normal-form
```
