# Inverting matching isomorphisms

These finite identities follow from cancellation. They are used to reverse
the orientation of a cone without discarding its matching witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PU

module SCT.VolumeI.Chapter01.Section05.InverseCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

isoInverse-unique : {C D : CAT} {f g : MAP C D}
  (α : =₁ f g) (β : =₁ g f) → =₂ (β ∙ α) (idIso f) → =₂ (invIso α) β
isoInverse-unique α β p = cancel-right-reflect α (invIso p ∙ isoComp-inverseˡ-at α)

inverse-identity : {C D : CAT} (f : MAP C D) → =₂ (invIso (idIso f)) (idIso f)
inverse-identity f = isoInverse-unique (idIso f) (idIso f) (isoComp-unitˡ-at (idIso f))

inverse-inverse : {C D : CAT} {f g : MAP C D} (α : =₁ f g) →
  =₂ (invIso (invIso α)) α
inverse-inverse α = isoInverse-unique (invIso α) α (isoComp-inverseʳ-at α)

inverse-composite : {C D : CAT} {f g h : MAP C D}
  (β : =₁ g h) (α : =₁ f g) →
  =₂ (invIso (β ∙ α)) (invIso α ∙ invIso β)
inverse-composite β α = isoInverse-unique (β ∙ α) (invIso α ∙ invIso β)
  (isoComp-inverseˡ-at α ∙
    (isoComp-cong (idIso (invIso α)) (cancel-left β α) ∙
      isoComp-assoc-at (invIso α) (invIso β) (β ∙ α)))

pre-inverse : {C D T : CAT} {f g : MAP C D} (α : =₁ f g) (r : MAP T C) →
  =₂ (invIso α ▷ r) (invIso (α ▷ r))
pre-inverse {f = f} α r = invIso (isoInverse-unique (α ▷ r) (invIso α ▷ r)
  (preWhisker-idIso f r ∙
    ((preWhisker r ◁ isoComp-inverseˡ-at α) ∙
      invIso (preWhisker-isoComp-at (invIso α) α r))))
```
