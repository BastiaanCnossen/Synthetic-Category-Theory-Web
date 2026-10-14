# Naturality of uncurried restriction frames

Changing a functor-valued diagram by an isomorphism changes its uncurried
restriction frame by the corresponding restricted uncurried isomorphism.
The formula retains the chosen comparison for parameter restriction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.RestrictedFrameNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module At {Γ Δ X C : CAT} {H K : MAP Γ (Fun X C)} (δ : H =₁ K) (i : MAP Δ Γ)
  {f : MAP Δ (Fun X C)} (p : (K ∘ i) =₁ f) where
  s : MAP (Δ × X) (Γ × X)
  s = productMap i (id X)
  h = funUncurry-restrict H i
  k = funUncurry-restrict K i
  d = funUncurryIso (δ ▷ i)
  e = funUncurryIso δ ▷ s
  r = funUncurryIso p

  abstract
    comparison : (funUncurryIso (p ∙ (δ ▷ i)) ∙ h ⁻¹) =₂
      ((r ∙ k ⁻¹) ∙ e)
    comparison = (isoComp-assoc-at r (k ⁻¹) e) ⁻¹ ∙
      isoComp-cong (idIso r) ((move-square k d e h (funUncurry-restrict-inputs δ i)) ⁻¹) ∙
      isoComp-assoc-at r d (h ⁻¹) ∙
      isoComp-cong (funUncurryIso-comp p (δ ▷ i)) (idIso (h ⁻¹))
```
