# Recovering a prescribed decoded leg

Naturality of decoding gives a square before endpoint changes. Cancelling
the naming and decoding comparisons recovers the prescribed original leg.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.DecodedLegCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

decoded-leg : {R S : CAT} {x₀ x₁ x₂ y₀ y₁ y₂ : MAP R S}
  (p : x₀ =₁ x₁) (q : y₀ =₁ y₁)
  (a : x₁ =₁ x₂) (b : y₁ =₁ y₂) (γ : x₂ =₁ y₂)
  (z : x₀ =₁ y₀) (w : x₁ =₁ y₁) →
  (q ∙ z) =₂ (w ∙ p) →
  z =₂ (q ⁻¹ ∙ (b ⁻¹ ∙ (γ ∙ (a ∙ p)))) →
  (changeEndpoints a b w) =₂ γ
decoded-leg p q a b γ z w natural image-β =
  square-to-changeEndpoints a b w γ square
  where
  image : (q ∙ z) =₂ (b ⁻¹ ∙ (γ ∙ (a ∙ p)))
  image = cancel-inverse q (b ⁻¹ ∙ (γ ∙ (a ∙ p))) ∙
    isoComp-cong (idIso q) image-β
  square : (b ∙ w) =₂ (γ ∙ a)
  square = cancel-right-reflect p
    ((isoComp-assoc-at γ a p) ⁻¹ ∙
      (cancel-inverse b (γ ∙ (a ∙ p)) ∙
        (isoComp-cong (idIso b) (image ∙ natural ⁻¹) ∙ isoComp-assoc-at b w p)))
```
