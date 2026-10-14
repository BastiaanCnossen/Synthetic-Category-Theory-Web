# Normalizing the restriction pentagon

The associator in the varying coordinate agrees with its two nested
coordinate presentations. The constant coordinate retains its left unitor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.NormalizedRestrictionPentagon
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)

module At {A B C D : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) (h : MAP C D) where
  π₁ : MAP (X × A) X
  π₁ = pr₁
  π₂ : MAP (X × A) A
  π₂ = pr₂
  left-coordinate : (((h ∘ g) ∘ f) ∘ π₂) =₁ (h ∘ (g ∘ (f ∘ π₂)))
  left-coordinate = comp-assoc (f ∘ π₂) g h ∙ comp-assoc π₂ f (h ∘ g)
  right-coordinate : ((h ∘ (g ∘ f)) ∘ π₂) =₁ (h ∘ (g ∘ (f ∘ π₂)))
  right-coordinate = (h ◁ comp-assoc π₂ f g) ∙ comp-assoc π₂ (g ∘ f) h
  left-frame : productMap (id X) ((h ∘ g) ∘ f) =₁ pair π₁ (h ∘ (g ∘ (f ∘ π₂)))
  left-frame = pair-cong (comp-unitˡ π₁) left-coordinate
  right-frame : productMap (id X) (h ∘ (g ∘ f)) =₁ pair π₁ (h ∘ (g ∘ (f ∘ π₂)))
  right-frame = pair-cong (comp-unitˡ π₁) right-coordinate

  abstract
    constant : (comp-unitˡ π₁ ∙ (idIso (id X) ▷ π₁)) =₂ comp-unitˡ π₁
    constant = isoComp-unitʳ-at (comp-unitˡ π₁) ∙
      isoComp-cong (idIso (comp-unitˡ π₁)) (preWhisker-idIso (id X) π₁)

    varying : (right-coordinate ∙ (comp-assoc f g h ▷ π₂)) =₂ left-coordinate
    varying = (pentagon-whiskered π₂ f g h) ⁻¹ ∙
      isoComp-assoc-at (h ◁ comp-assoc π₂ f g) (comp-assoc π₂ (g ∘ f) h)
        (comp-assoc f g h ▷ π₂)

    value : (right-frame ∙ productMap-cong (idIso (id X)) (comp-assoc f g h)) =₂ left-frame
    value = pair-cong-Iso₂ constant varying ∙
      (pair-cong-comp (comp-unitˡ π₁) (idIso (id X) ▷ π₁) right-coordinate (comp-assoc f g h ▷ π₂)) ⁻¹
```
