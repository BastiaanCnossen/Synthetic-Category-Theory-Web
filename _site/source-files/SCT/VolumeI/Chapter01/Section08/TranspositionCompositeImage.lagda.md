# The associator under transposition

Successive substitutions under uncurrying give the evaluated associator.
Restriction along the product symmetry then gives the transposed version.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section08.TranspositionCompositeImage
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.SubstitutionCoherence 𝒯 M ℱ
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
  ν = funUncurry-restrict h (g ∘ f)
  uncurried-associator = funUncurryIso (comp-assoc f g h)
  action = transposeIso (comp-assoc f g h)
  leading = (e ◁ κ) ∙
    (comp-assoc Yf Yg e ∙ ((funUncurry-restrict h g ▷ Yf) ∙ funUncurry-restrict (h ∘ g) f))
  r₁ = ν ▷ HA
  r₂ = comp-assoc HA Ygf e
  r₃ = e ◁ swap-restriction (g ∘ f)
  r₄ = (comp-assoc Xgf HC e) ⁻¹
  prefix = r₄ ∙ (r₃ ∙ r₂)

  abstract
    normalize : (transpose-pre (g ∘ f) h) =₂ (prefix ∙ r₁)
    normalize = (isoComp-assoc-at r₄ (r₃ ∙ r₂) r₁) ⁻¹ ∙
      isoComp-cong (idIso r₄) ((isoComp-assoc-at r₃ r₂ r₁) ⁻¹)

    restricted : (r₁ ∙ action) =₂ (leading ▷ HA)
    restricted = (preWhisker HA ◁ funUncurry-restrict-iterated h g f) ∙
      ((preWhisker-isoComp-at ν uncurried-associator HA) ⁻¹ ∙
        isoComp-cong (idIso r₁) (transposeIso-at (comp-assoc f g h)))

    law : (transpose-pre (g ∘ f) h ∙ transposeIso (comp-assoc f g h)) =₂
      (prefix ∙ (leading ▷ HA))
    law = isoComp-cong (idIso prefix) restricted ∙
      (isoComp-assoc-at prefix r₁ action ∙ isoComp-cong normalize (idIso action))
```
