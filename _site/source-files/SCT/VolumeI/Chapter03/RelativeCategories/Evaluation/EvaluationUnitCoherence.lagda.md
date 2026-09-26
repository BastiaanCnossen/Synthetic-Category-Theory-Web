# The unit comparison for evaluation

The two unitors agree on an identity functor. This derived coherence is
used when the terminal parameter of a named relative functor is removed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as PFU
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorCoherence as PFC

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.EvaluationUnitCoherence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at; postWhisker-comp-at; preWhisker-id-at)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (preWhisker-id-reflect; triangle-whiskered; right-unitor-comp)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect; cancel-right)
open PFU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp; productMap-unitʳ; productMap-id-triangle₂)


abstract
  identity-unitors : (C : CAT) → comp-unitʳ (id C) =₂ comp-unitˡ (id C)
  identity-unitors C = preWhisker-id-reflect
    (left-unitor-comp (id C) (id C) ∙
      (isoComp-cong (cancel-left-reflect (comp-unitˡ (id C)) (postWhisker-id-at (comp-unitˡ (id C))))
        (idIso (comp-assoc (id C) (id C) (id C))) ∙ triangle-whiskered (id C) (id C)))

unit-at-product : {X C D : CAT} (h : MAP (X × C) D) →
  (h ∘ productMap (id X) (id C)) =₁ h
unit-at-product {X} {C} h = comp-unitʳ h ∙ (h ◁ productMap-id X C)

module PostUnit {X C D E : CAT} (h : MAP (X × C) D) (e : MAP D E) where
  d : productMap (id X) (id C) =₁ id (X × C)
  d = productMap-id X C
  A : ((e ∘ h) ∘ productMap (id X) (id C)) =₁
    (e ∘ (h ∘ productMap (id X) (id C)))
  A = comp-assoc (productMap (id X) (id C)) h e

  abstract
    comparison : unit-at-product (e ∘ h) =₂ ((e ◁ unit-at-product h) ∙ A)
    comparison = isoComp-cong ((postWhisker-isoComp-at e (comp-unitʳ h) (h ◁ d)) ⁻¹) (idIso A) ∙
      ((isoComp-assoc-at (e ◁ comp-unitʳ h) (e ◁ (h ◁ d)) A) ⁻¹ ∙
        (isoComp-cong (idIso (e ◁ comp-unitʳ h)) (postWhisker-comp-at d h e) ∙
          (isoComp-assoc-at (e ◁ comp-unitʳ h) (comp-assoc (id (X × C)) h e) ((e ∘ h) ◁ d) ∙
            isoComp-cong (right-unitor-comp h e) (idIso ((e ∘ h) ◁ d)))))

    cancel-associator : (unit-at-product (e ∘ h) ∙ A ⁻¹) =₂ (e ◁ unit-at-product h)
    cancel-associator = cancel-right A (e ◁ unit-at-product h) ∙
      isoComp-cong comparison (idIso (A ⁻¹))

module UncurryUnit {X C D : CAT} (F : MAP X (Fun C D)) where
  h : MAP (X × C) (Fun C D × C)
  h = productMap F (id C)
  e : MAP (Fun C D × C) D
  e = funEval
  σ : (h ∘ productMap (id X) (id C)) =₁ productMap (F ∘ id X) (id C)
  σ = slice-comparison F (id X)
  α : productMap (F ∘ id X) (id C) =₁ h
  α = productMap-cong (comp-unitʳ F) (idIso (id C))

  abstract
    product-comparison : (α ∙ σ) =₂ unit-at-product h
    product-comparison = productMap-unitʳ F (id C) ∙
      (isoComp-cong
        (productMap-cong-Iso₂ (isoComp-unitʳ-at (comp-unitʳ F))
          ((identity-unitors C) ⁻¹ ∙ isoComp-unitˡ-at (comp-unitˡ (id C))) ∙
          (productMap-cong-comp (comp-unitʳ F) (idIso (F ∘ id X))
            (idIso (id C)) (comp-unitˡ (id C))) ⁻¹)
        (idIso (productMap-comp (id X) F (id C) (id C))) ∙
        (isoComp-assoc-at α
          (productMap-cong (idIso (F ∘ id X)) (comp-unitˡ (id C)))
          (productMap-comp (id X) F (id C) (id C))) ⁻¹)

    normalization :
      (unit-at-product (funUncurry F) ∙ funUncurry-restrict F (id X)) =₂ (e ◁ α)
    normalization = (postWhisker e ◁ cancel-right σ α) ∙
      ((postWhisker-isoComp-at e (α ∙ σ) (σ ⁻¹)) ⁻¹ ∙
        (isoComp-cong ((postWhisker e ◁ product-comparison) ⁻¹) (idIso (e ◁ σ ⁻¹)) ∙
          (isoComp-cong (PostUnit.cancel-associator h e) (idIso (e ◁ σ ⁻¹)) ∙
            (isoComp-assoc-at (unit-at-product (funUncurry F)) (PostUnit.A h e ⁻¹) (e ◁ σ ⁻¹)) ⁻¹)))

    comparison : funUncurryIso (comp-unitʳ F) =₂
      (unit-at-product (funUncurry F) ∙ funUncurry-restrict F (id X))
    comparison = normalization ⁻¹ ∙ funUncurryIso-at (comp-unitʳ F)
```
