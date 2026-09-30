# Uncurrying and the composition unitors

The left and right unit laws for substitution identify the images of
composition unitors under uncurrying. These formulas retain the chosen
product substitutions and evaluation comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.UncurryingUnits
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitutionUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.RestrictedFrames as Restricted
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered; right-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; postWhisker-comp-at)

module At {Γ K C : CAT} (h : MAP Γ (Fun K C)) where
  π : MAP (Γ × K) (Fun K C × K)
  π = productMap h (id K)
  e : MAP (Fun K C × K) C
  e = funEval
  J : MAP (Fun K C × K) (Fun K C × K)
  J = productMap (id (Fun K C)) (id K)
  j : MAP (Γ × K) (Γ × K)
  j = productMap (id Γ) (id K)
  δ = productMap-id (Fun K C) K
  γ = productMap-id Γ K
  module Product = ProductUnits.At 𝒯 M K h
  module Left = Restricted.At 𝒯 M ℱ (id (Fun K C)) h (comp-unitˡ h)
  module Right = Restricted.At 𝒯 M ℱ h (id Γ) (comp-unitʳ h)

  abstract
    left-core : (funUncurryIso (comp-unitˡ h) ∙ (funUncurry-restrict (id (Fun K C)) h) ⁻¹) =₂
      (funUncurry-id K C ▷ π)
    left-core = (preWhisker-isoComp-at (comp-unitʳ e) (e ◁ δ) π) ⁻¹ ∙
      isoComp-cong ((triangle-whiskered π e) ⁻¹) (idIso ((e ◁ δ) ▷ π)) ∙
      (isoComp-assoc-at (e ◁ comp-unitˡ π) (comp-assoc π (id _) e) ((e ◁ δ) ▷ π)) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ comp-unitˡ π)) ((whisker-mixed-at δ π e) ⁻¹) ∙
      isoComp-assoc-at (e ◁ comp-unitˡ π) (e ◁ (δ ▷ π)) (comp-assoc π J e) ∙
      isoComp-cong (postWhisker-isoComp-at e (comp-unitˡ π) (δ ▷ π)) (idIso (comp-assoc π J e)) ∙
      isoComp-cong (postWhisker e ◁ Product.left) (idIso (comp-assoc π J e)) ∙ Left.comparison

    left : funUncurryIso (comp-unitˡ h) =₂
      ((funUncurry-id K C ▷ π) ∙ funUncurry-restrict (id (Fun K C)) h)
    left = isoComp-cong left-core (idIso (funUncurry-restrict (id (Fun K C)) h)) ∙
      (cancel-inverse-tail (funUncurryIso (comp-unitˡ h)) (funUncurry-restrict (id (Fun K C)) h)) ⁻¹

    right-core : (funUncurryIso (comp-unitʳ h) ∙ (funUncurry-restrict h (id Γ)) ⁻¹) =₂
      (comp-unitʳ (funUncurry h) ∙ (funUncurry h ◁ γ))
    right-core = isoComp-cong ((right-unitor-comp π e) ⁻¹) (idIso ((e ∘ π) ◁ γ)) ∙
      (isoComp-assoc-at (e ◁ comp-unitʳ π) (comp-assoc (id _) π e) ((e ∘ π) ◁ γ)) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ comp-unitʳ π)) ((postWhisker-comp-at γ π e) ⁻¹) ∙
      isoComp-assoc-at (e ◁ comp-unitʳ π) (e ◁ (π ◁ γ)) (comp-assoc j π e) ∙
      isoComp-cong (postWhisker-isoComp-at e (comp-unitʳ π) (π ◁ γ)) (idIso (comp-assoc j π e)) ∙
      isoComp-cong (postWhisker e ◁ Product.right) (idIso (comp-assoc j π e)) ∙ Right.comparison

    right : funUncurryIso (comp-unitʳ h) =₂
      (comp-unitʳ (funUncurry h) ∙ ((funUncurry h ◁ γ) ∙ funUncurry-restrict h (id Γ)))
    right = isoComp-assoc-at (comp-unitʳ (funUncurry h)) (funUncurry h ◁ γ) (funUncurry-restrict h (id Γ)) ∙
      isoComp-cong right-core (idIso (funUncurry-restrict h (id Γ))) ∙
      (cancel-inverse-tail (funUncurryIso (comp-unitʳ h)) (funUncurry-restrict h (id Γ))) ⁻¹
```
