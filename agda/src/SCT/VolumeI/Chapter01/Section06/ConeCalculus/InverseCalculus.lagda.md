# Inverting matching isomorphisms

These finite identities follow from cancellation. They are used to reverse
the orientation of a cone without discarding its matching witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

isoInverse-unique : {C D : CAT} {f g : MAP C D}
  (α : f =₁ g) (β : g =₁ f) → (β ∙ α) =₂ (idIso f) → (α ⁻¹) =₂ β
isoInverse-unique α β p = cancel-right-reflect α (p ⁻¹ ∙ isoComp-inverseˡ-at α)

inverse-identity : {C D : CAT} (f : MAP C D) → ((idIso f) ⁻¹) =₂ (idIso f)
inverse-identity f = isoInverse-unique (idIso f) (idIso f) (isoComp-unitˡ-at (idIso f))

inverse-inverse : {C D : CAT} {f g : MAP C D} (α : f =₁ g) →
  ((α ⁻¹) ⁻¹) =₂ α
inverse-inverse α = isoInverse-unique (α ⁻¹) α (isoComp-inverseʳ-at α)

inverse-composite : {C D : CAT} {f g h : MAP C D}
  (β : g =₁ h) (α : f =₁ g) →
  ((β ∙ α) ⁻¹) =₂ (α ⁻¹ ∙ β ⁻¹)
inverse-composite β α = isoInverse-unique (β ∙ α) (α ⁻¹ ∙ β ⁻¹)
  (isoComp-inverseˡ-at α ∙
    (isoComp-cong (idIso (α ⁻¹)) (cancel-left β α) ∙
      isoComp-assoc-at (α ⁻¹) (β ⁻¹) (β ∙ α)))

pre-inverse : {C D T : CAT} {f g : MAP C D} (α : f =₁ g) (r : MAP T C) →
  (α ⁻¹ ▷ r) =₂ ((α ▷ r) ⁻¹)
pre-inverse {f = f} α r = (isoInverse-unique (α ▷ r) (α ⁻¹ ▷ r)
  (preWhisker-idIso f r ∙
    ((preWhisker r ◁ isoComp-inverseˡ-at α) ∙
      (preWhisker-isoComp-at (α ⁻¹) α r) ⁻¹))) ⁻¹
```
