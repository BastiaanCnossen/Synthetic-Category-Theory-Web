# Reflecting higher identifications after restriction

When restriction on mapping animae is an equivalence, equality of the
restricted identifications reflects to equality of the original ones.
Naming, decoding, and their prescribed comparisons reduce this to
reflection through the equivalence on the mapping anima. This is used
to retain the matching when lifting comparisons of cocones.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.RestrictionReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingCalculus 𝒯 M using (decodePre; decodePre-absolute)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)

module Reflection {A B E : CAT} (i : MAP A B) (ei : IsEquiv (mapPre {D = E} i))
  {f g : MAP B E} (α β : f =₁ g) (image : (α ▷ i) =₂ (β ▷ i)) where
  f′ = nameMap f
  g′ = nameMap g
  df = decode-name f
  dg = decode-name g
  raw : (γ : f =₁ g) → decodeMap f′ =₁ decodeMap g′
  raw γ = dg ⁻¹ ∙ (γ ∙ df)
  encoded : (γ : f =₁ g) → f′ =₁ g′
  encoded γ = decodeMap-reflect f′ g′ (raw γ)
  restricted : (γ : f =₁ g) → (mapPre i ∘ f′) =₁ (mapPre i ∘ g′)
  restricted γ = mapPre i ◁ encoded γ

  abstract
    raw-restriction : (γ : f =₁ g) → (raw γ ▷ i) =₂
      ((dg ⁻¹ ▷ i) ∙ ((γ ▷ i) ∙ (df ▷ i)))
    raw-restriction γ = isoComp-cong (idIso (dg ⁻¹ ▷ i)) (preWhisker-isoComp-at γ df i) ∙
      preWhisker-isoComp-at (dg ⁻¹) (γ ∙ df) i

    decoded-restriction : (decodeMapIso (encoded α) ▷ i) =₂ (decodeMapIso (encoded β) ▷ i)
    decoded-restriction = (preWhisker i ◁ (decodeMap-reflect-β f′ g′ (raw β)) ⁻¹) ∙
      ((raw-restriction β) ⁻¹ ∙
        (isoComp-cong (idIso (dg ⁻¹ ▷ i)) (isoComp-cong image (idIso (df ▷ i))) ∙
          (raw-restriction α ∙ (preWhisker i ◁ decodeMap-reflect-β f′ g′ (raw α)))))

    named-image : restricted α =₂ restricted β
    named-image = decodeMap-reflect-Iso₂ (restricted α) (restricted β)
      (cancel-left-reflect (decodePre i g′)
        ((decodePre-absolute i (encoded β)) ⁻¹ ∙
          (isoComp-cong decoded-restriction (idIso (decodePre i f′)) ∙
            decodePre-absolute i (encoded α))))

    named : encoded α =₂ encoded β
    named = equiv-reflect (postWhisker-isEquiv (mapPre i) ei f′ g′) _ _ named-image

    comparison : α =₂ β
    comparison = cancel-right-reflect df (cancel-left-reflect (dg ⁻¹)
      (decodeMap-reflect-β f′ g′ (raw β) ∙
        (decodeMap-Iso₂ named ∙ (decodeMap-reflect-β f′ g′ (raw α)) ⁻¹)))

abstract
  restriction-reflect-Iso₂ : {A B E : CAT} (i : MAP A B) → IsEquiv (mapPre {D = E} i) →
    {f g : MAP B E} (α β : f =₁ g) → (α ▷ i) =₂ (β ▷ i) → α =₂ β
  restriction-reflect-Iso₂ i ei α β image = Reflection.comparison i ei α β image
```
