# Images of normalized restriction coordinates

Applying a product functor after normalizing an inner composite gives the
specified product restriction compositor with the nested target frame.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionImage
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality 𝒯 M using (productMap-pair-inner)
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductPairingComparisons as Pairs
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp; pair-cong-Iso₂)
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)

module At {A B C D : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) (h : MAP C D) where
  π₁ : MAP (X × A) X
  π₁ = pr₁
  π₂ : MAP (X × A) A
  π₂ = pr₂
  z : MAP A C
  z = g ∘ f
  W : MAP (X × C) (X × D)
  W = productMap (id X) h
  λ₁ = comp-unitˡ π₁
  τ = comp-assoc π₂ f g
  first-assoc = comp-assoc π₁ (id X) (id X)
  second-assoc = comp-assoc π₂ z h
  δ = pair-cong λ₁ τ
  P₀ = productMap-pair (id X) h (id X ∘ π₁) (z ∘ π₂)
  P₁ = productMap-pair (id X) h π₁ (g ∘ (f ∘ π₂))
  χ = pair-cong λ₁ (idIso (h ∘ (g ∘ (f ∘ π₂)))) ∙ P₁
  ψ = χ ∙ (W ◁ δ)
  δR = pair-cong λ₁ ((h ◁ τ) ∙ second-assoc)
  first-image = comp-unitˡ (id X) ▷ π₁
  second-image = idIso (h ∘ z) ▷ π₂
  first-normal = λ₁ ∙ (id X ◁ λ₁)
  normal = pair-cong first-normal (h ◁ τ) ∙ P₀
  module Raw = Pairs.ProductPair 𝒯 M (id X) h (id X ∘ π₁) (z ∘ π₂)
    (first-assoc ⁻¹) (second-assoc ⁻¹)

  abstract
    left-normalization : ψ =₂ normal
    left-normalization = isoComp-cong
        (pair-cong-Iso₂ (idIso first-normal) (isoComp-unitˡ-at (h ◁ τ))) (idIso P₀) ∙
      isoComp-cong ((pair-cong-comp λ₁ (id X ◁ λ₁) (idIso (h ∘ (g ∘ (f ∘ π₂)))) (h ◁ τ)) ⁻¹) (idIso P₀) ∙
      (isoComp-assoc-at (pair-cong λ₁ (idIso (h ∘ (g ∘ (f ∘ π₂)))))
        (pair-cong (id X ◁ λ₁) (h ◁ τ)) P₀) ⁻¹ ∙
      isoComp-cong (idIso (pair-cong λ₁ (idIso (h ∘ (g ∘ (f ∘ π₂))))))
        (productMap-pair-inner (id X) h λ₁ τ) ∙
      isoComp-assoc-at (pair-cong λ₁ (idIso (h ∘ (g ∘ (f ∘ π₂))))) P₁ (W ◁ δ)

    unitor-solved : comp-unitˡ (id X ∘ π₁) =₂ (first-image ∙ first-assoc ⁻¹)
    unitor-solved = isoComp-cong (left-unitor-comp π₁ (id X)) (idIso (first-assoc ⁻¹)) ∙
      (cancel-right first-assoc (comp-unitˡ (id X ∘ π₁))) ⁻¹

    first-comparison : (λ₁ ∙ (first-image ∙ first-assoc ⁻¹)) =₂ first-normal
    first-comparison = (isoComp-cong (idIso λ₁) unitor-solved ∙ postWhisker-id-at λ₁) ⁻¹

    second-comparison : (((h ◁ τ) ∙ second-assoc) ∙ (second-image ∙ second-assoc ⁻¹)) =₂ (h ◁ τ)
    second-comparison = cancel-right second-assoc (h ◁ τ) ∙
      isoComp-cong (idIso ((h ◁ τ) ∙ second-assoc))
        (isoComp-unitˡ-at (second-assoc ⁻¹) ∙
          isoComp-cong (preWhisker-idIso (h ∘ z) π₂) (idIso (second-assoc ⁻¹)))

    compositor-normalization : productRestriction-comp X z h =₂
      (pair-cong (first-image ∙ first-assoc ⁻¹) (second-image ∙ second-assoc ⁻¹) ∙ P₀)
    compositor-normalization = isoComp-cong
        ((pair-cong-comp first-image (first-assoc ⁻¹) second-image (second-assoc ⁻¹)) ⁻¹) (idIso P₀) ∙
      (isoComp-assoc-at (pair-cong first-image second-image) (pair-cong (first-assoc ⁻¹) (second-assoc ⁻¹)) P₀) ⁻¹ ∙
      isoComp-cong (idIso (pair-cong first-image second-image)) (Raw.normalization ⁻¹)

    right-normalization : (δR ∙ productRestriction-comp X z h) =₂ normal
    right-normalization = isoComp-cong (pair-cong-Iso₂ first-comparison second-comparison) (idIso P₀) ∙
      isoComp-cong ((pair-cong-comp λ₁ (first-image ∙ first-assoc ⁻¹)
        ((h ◁ τ) ∙ second-assoc) (second-image ∙ second-assoc ⁻¹)) ⁻¹) (idIso P₀) ∙
      (isoComp-assoc-at δR (pair-cong (first-image ∙ first-assoc ⁻¹) (second-image ∙ second-assoc ⁻¹)) P₀) ⁻¹ ∙
      isoComp-cong (idIso δR) compositor-normalization

    value : ψ =₂ (δR ∙ productRestriction-comp X z h)
    value = right-normalization ⁻¹ ∙ left-normalization
```
