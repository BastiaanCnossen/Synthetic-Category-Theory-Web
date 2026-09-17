# Recovering a prescribed decoded leg

Naturality of decoding gives a square before endpoint changes. Cancelling
the naming and decoding comparisons recovers the prescribed original leg.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.DecodedLegCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

decoded-leg : {R S : CAT} {x₀ x₁ x₂ y₀ y₁ y₂ : MAP R S}
  (p : NatIso x₀ x₁) (q : NatIso y₀ y₁)
  (a : NatIso x₁ x₂) (b : NatIso y₁ y₂) (γ : NatIso x₂ y₂)
  (z : NatIso x₀ y₀) (w : NatIso x₁ y₁) →
  Iso₂ (q ∙ z) (w ∙ p) →
  Iso₂ z (invIso q ∙ (invIso b ∙ (γ ∙ (a ∙ p)))) →
  Iso₂ (changeEndpoints a b w) γ
decoded-leg p q a b γ z w natural image-β =
  square-to-changeEndpoints a b w γ square
  where
  image : Iso₂ (q ∙ z) (invIso b ∙ (γ ∙ (a ∙ p)))
  image = cancel-inverse q (invIso b ∙ (γ ∙ (a ∙ p))) ∙
    isoComp-cong (idIso q) image-β
  square : Iso₂ (b ∙ w) (γ ∙ a)
  square = cancel-right-reflect p
    (invIso (isoComp-assoc-at γ a p) ∙
      (cancel-inverse b (γ ∙ (a ∙ p)) ∙
        (isoComp-cong (idIso b) (image ∙ invIso natural) ∙ isoComp-assoc-at b w p)))
```
