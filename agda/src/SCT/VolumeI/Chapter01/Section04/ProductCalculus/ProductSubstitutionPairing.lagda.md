# Product substitution from the pairing comparison

The comparison for applying a product functor to a pair reduces to the
chosen substitution comparison after the first associator and the identity
coordinate are normalized.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitutionPairing
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductPairingComparisons as Pairing
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as Substitution
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PC vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-Iso₂)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module At {Γ A B : CAT} (X : CAT) (F : MAP A B) (f : MAP Γ A) where
  fixed : MAP (Γ × X) X
  fixed = id X ∘ pr₂
  first-frame : (F ∘ (f ∘ pr₁ {Γ} {X})) =₁ ((F ∘ f) ∘ pr₁)
  first-frame = (comp-assoc pr₁ f F) ⁻¹
  second-frame : (id X ∘ fixed) =₁ fixed
  second-frame = comp-unitˡ fixed
  module Pair = Pairing.ProductPair 𝒯 M F (id X) (f ∘ pr₁) fixed first-frame second-frame
  module Product = Substitution.Coordinates 𝒯 M X F f
  A₂ : ((id X ∘ id X) ∘ pr₂ {Γ} {X}) =₁ (id X ∘ fixed)
  A₂ = comp-assoc pr₂ (id X) (id X)
  C₂ : ((id X ∘ pr₂) ∘ productMap f (id X)) =₁ (id X ∘ fixed)
  C₂ = (id X ◁ pair-β₂ (f ∘ pr₁) fixed) ∙ comp-assoc (productMap f (id X)) pr₂ (id X)
  unit-image : ((id X ∘ id X) ∘ pr₂ {Γ} {X}) =₁ fixed
  unit-image = comp-unitˡ (id X) ▷ pr₂

  abstract
    unit-normalization : second-frame =₂ (unit-image ∙ A₂ ⁻¹)
    unit-normalization = isoComp-cong (left-unitor-comp (pr₂ {Γ} {X}) (id X)) (idIso (A₂ ⁻¹)) ∙
      (cancel-right A₂ second-frame) ⁻¹

    second-normalization : Pair.second =₂ Product.second
    second-normalization = isoComp-assoc-at unit-image (A₂ ⁻¹) C₂ ∙
      isoComp-cong unit-normalization (idIso C₂)

    comparison : Pair.comparison =₂ slice-comparison F f
    comparison = Product.normalization ⁻¹ ∙
      isoComp-cong (pair-cong-Iso₂ (idIso Product.first) second-normalization)
        (idIso (pair-pre (F ∘ pr₁) (id X ∘ pr₂) (productMap f (id X)))) ∙ Pair.normalization
```
