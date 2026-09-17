# The associator under transposition

Successive substitutions under uncurrying give the evaluated associator.
Restriction along the product symmetry then gives the transposed version.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section08.TranspositionCompositeImage
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.SubstitutionCoherence 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯

module CompositorImage {X A B C E : CAT}
  (f : MAP A B) (g : MAP B C) (h : MAP C (Fun X E)) where
  e = funUncurry h
  HA = swap {X} {A}
  HC = swap {X} {C}
  Yf = productMap f (id X)
  Yg = productMap g (id X)
  Ygf = productMap (g ∘ f) (id X)
  Xgf = productRestriction X (g ∘ f)
  κ = slice-comparison {C = X} g f
  ν = funUncurry-pre h (g ∘ f)
  uncurried-associator = funUncurryIso (comp-assoc f g h)
  action = transposeIso (comp-assoc f g h)
  leading = (e ◁ κ) ∙
    (comp-assoc Yf Yg e ∙ ((funUncurry-pre h g ▷ Yf) ∙ funUncurry-pre (h ∘ g) f))
  r₁ = ν ▷ HA
  r₂ = comp-assoc HA Ygf e
  r₃ = e ◁ swap-restriction (g ∘ f)
  r₄ = invIso (comp-assoc Xgf HC e)
  prefix = r₄ ∙ (r₃ ∙ r₂)

  abstract
    normalize : =₂ (transpose-pre (g ∘ f) h) (prefix ∙ r₁)
    normalize = invIso (isoComp-assoc-at r₄ (r₃ ∙ r₂) r₁) ∙
      isoComp-cong (idIso r₄) (invIso (isoComp-assoc-at r₃ r₂ r₁))

    restricted : =₂ (r₁ ∙ action) (leading ▷ HA)
    restricted = (preWhisker HA ◁ funUncurry-pre-iterated h g f) ∙
      (invIso (preWhisker-isoComp-at ν uncurried-associator HA) ∙
        isoComp-cong (idIso r₁) (transposeIso-at (comp-assoc f g h)))

    law : =₂ (transpose-pre (g ∘ f) h ∙ transposeIso (comp-assoc f g h))
      (prefix ∙ (leading ▷ HA))
    law = isoComp-cong (idIso prefix) restricted ∙
      (isoComp-assoc-at prefix r₁ action ∙ isoComp-cong normalize (idIso action))
```
