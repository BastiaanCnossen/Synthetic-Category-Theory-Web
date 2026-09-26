# Successive restrictions of functor-category uncurrying

The product-substitution associativity proof from Chapter 1 applies to
functor-category evaluation as well. This transfers that checked proof
to the existing uncurrying comparisons, without choosing replacement
associators or adding a coherence assumption.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Parameterized

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Substitution.IteratedCompatibility 𝒯 M using (evaluation-step-iterated)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (slice-comparison-assoc)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pre-inverse-at; solve-pentagon)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-at)

module Iteration {W Y X C D : CAT}
  (f : MAP X (Fun C D)) (σ : MAP Y X) (τ : MAP W Y) where

  F : {A B : CAT} → MAP A B → MAP (A × C) (B × C)
  F h = productMap h (id C)

  κ : {A B Z : CAT} (h : MAP B Z) (r : MAP A B)
    → (F h ∘ F r) =₁ (F (h ∘ r))
  κ = slice-comparison

  ProductAssociativity : Set m
  ProductAssociativity =
    (κ f (σ ∘ τ) ∙ ((F f ◁ κ σ τ) ∙ comp-assoc (F τ) (F σ) (F f))) =₂
    (productMap-cong (comp-assoc τ σ f) (idIso (id C)) ∙
      (κ (f ∘ σ) τ ∙ (κ f σ ▷ F τ)))

  together : (funUncurry ((f ∘ σ) ∘ τ)) =₁ (funUncurry f ∘ F (σ ∘ τ))
  together = funUncurry-restrict f (σ ∘ τ) ∙ funUncurryIso (comp-assoc τ σ f)

  successively : (funUncurry ((f ∘ σ) ∘ τ)) =₁ (funUncurry f ∘ F (σ ∘ τ))
  successively = (funUncurry f ◁ κ σ τ) ∙
    (comp-assoc (F τ) (F σ) (funUncurry f) ∙
      ((funUncurry-restrict f σ ▷ F τ) ∙ funUncurry-restrict (f ∘ σ) τ))

  transfer : ProductAssociativity → together =₂ successively
  transfer product-assoc =
    (isoComp-cong (idIso (funUncurry-restrict f (σ ∘ τ))) ((funUncurryIso-at (comp-assoc τ σ f)) ⁻¹) ∙
    let p = F f
        s = F σ
        t = F τ
        e = funEval
        k = κ σ τ
        a = (κ f σ) ⁻¹
        b = (κ (f ∘ σ) τ) ⁻¹
        inner = comp-assoc t s p ∙ ((a ▷ t) ∙ b)
        outside = (comp-assoc (F (σ ∘ τ)) p e) ⁻¹
        middle = (comp-assoc (s ∘ t) p e) ⁻¹
        whiskered-k = p ◁ k
        associator = productMap-cong (comp-assoc τ σ f) (idIso (id C))
        commute = (move-square (comp-assoc (F (σ ∘ τ)) p e)
          (funUncurry f ◁ k) (e ◁ whiskered-k) (comp-assoc (s ∘ t) p e)
          (postWhisker-comp-at k p e)) ⁻¹
        solve = solve-pentagon (κ f (σ ∘ τ)) (whiskered-k ∙ comp-assoc t s p)
          associator (κ (f ∘ σ) τ) (κ f σ ▷ t) product-assoc ∙
          ((isoComp-assoc-at whiskered-k (comp-assoc t s p)
            ((κ f σ ▷ t) ⁻¹ ∙ b)) ⁻¹ ∙
            isoComp-cong (idIso whiskered-k)
              (isoComp-cong (idIso (comp-assoc t s p))
                (isoComp-cong (pre-inverse-at (κ f σ) t) (idIso b))))
    in (isoComp-assoc-at outside (e ◁ (κ f (σ ∘ τ)) ⁻¹) (e ◁ associator)) ⁻¹ ∙
      (isoComp-cong (idIso outside) (postWhisker-isoComp-at e ((κ f (σ ∘ τ)) ⁻¹) associator) ∙
      (isoComp-cong (idIso outside) (postWhisker e ◁ solve) ∙
      (isoComp-cong (idIso outside) ((postWhisker-isoComp-at e whiskered-k inner) ⁻¹) ∙
      (isoComp-assoc-at outside (e ◁ whiskered-k) (e ◁ inner) ∙
      (isoComp-cong commute (idIso (e ◁ inner)) ∙
      ((isoComp-assoc-at (funUncurry f ◁ k) middle (e ◁ inner)) ⁻¹ ∙
        isoComp-cong (idIso (funUncurry f ◁ k))
          (evaluation-step-iterated e p s t a b)))))))) ⁻¹

  abstract
    coherence : together =₂ successively
    coherence = transfer (slice-comparison-assoc C f σ τ)
```
