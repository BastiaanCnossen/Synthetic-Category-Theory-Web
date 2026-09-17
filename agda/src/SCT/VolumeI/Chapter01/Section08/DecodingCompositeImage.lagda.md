# The restriction compositor under decoding

The evaluated compositor restricts along the terminal-product inclusion.
The external associator remains on the input side of this comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section08.PrecompositionComposition as CompositionAt

module SCT.VolumeI.Chapter01.Section08.DecodingCompositeImage
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.DecodingNaturality 𝒯 M using (oneProduct-natural; decodePre)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus 𝒯 using (append-four)

module CompositorImage {A B C E : CAT}
  (f : MAP A B) (g : MAP B C) (h : Obj-abs (Map C E)) where
  e = mapUncurry h
  HA = oneProduct-in A
  HC = oneProduct-in C
  Yf = productRestriction One f
  Yg = productRestriction One g
  Ygf = productRestriction One (g ∘ f)
  κ = productRestriction-comp One f g
  ν = mapPre-uncurry (g ∘ f) h
  input-associator = comp-assoc h (mapPre g) (mapPre f)
  uncurried-associator = mapUncurryIso input-associator
  τ = decodeMapIso input-associator
  compositor = mapPre-comp f g ▷ h
  action = decodeMapIso compositor
  image = mapUncurryIso compositor
  p = e ◁ κ
  b = comp-assoc Yf Yg e
  q = mapPre-uncurry g h ▷ Yf
  μ = mapPre-uncurry f (mapPre g ∘ h)
  leading = p ∙ (b ∙ (q ∙ μ))
  r₁ = ν ▷ HA
  r₂ = comp-assoc HA Ygf e
  r₃ = e ◁ oneProduct-natural (g ∘ f)
  r₄ = invIso (comp-assoc (g ∘ f) HC e)
  prefix = r₄ ∙ (r₃ ∙ r₂)

  abstract
    normalize : =₂ (decodePre (g ∘ f) h) (prefix ∙ r₁)
    normalize = invIso (isoComp-assoc-at r₄ (r₃ ∙ r₂) r₁) ∙
      isoComp-cong (idIso r₄) (invIso (isoComp-assoc-at r₃ r₂ r₁))

    restricted : =₂ (r₁ ∙ action) ((leading ▷ HA) ∙ τ)
    restricted = isoComp-cong (idIso (leading ▷ HA)) (invIso (decodeMapIso-at input-associator)) ∙
      (preWhisker-isoComp-at leading uncurried-associator HA ∙
      ((preWhisker HA ◁
        (invIso (append-four p b q μ uncurried-associator) ∙
          CompositionAt.CompositorEvaluation.comparison 𝒯 M f g h)) ∙
      (invIso (preWhisker-isoComp-at ν image HA) ∙
        isoComp-cong (idIso r₁) (decodeMapIso-at compositor))))

    law : =₂ (decodePre (g ∘ f) h ∙ decodeMapIso compositor)
      (prefix ∙ ((leading ▷ HA) ∙ τ))
    law = isoComp-cong (idIso prefix) restricted ∙
      (isoComp-assoc-at prefix r₁ action ∙ isoComp-cong normalize (idIso action))
```
