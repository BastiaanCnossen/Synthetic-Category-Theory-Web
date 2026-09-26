# Endpoint evaluation of the identity restriction

The identity restriction has the specified product unitor as its
uncurried comparison. Evaluating it at an object gives the same path as
restricting to that object and then applying its left unitor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.UniversalArrowEvaluation as Universal
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.IdentityRestrictionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertions 𝒯 M ℱ using (insertion)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Product {A : CAT} (X : CAT) (x : Obj-abs A) where
  i = insert {X = X} x
  vertex = pair-cong (idIso (id X)) (comp-unitˡ x ▷ terminate X)
  χ = insertion X (id A) x
  δ = productMap-id X A
  close = pair-cong (comp-unitˡ (id X)) ((comp-assoc (terminate X) x (id A)) ⁻¹)
  step = productMap-pair (id X) (id A) (id X) (const x)

  abstract
    constant-coordinate :
      ((comp-unitˡ x ▷ terminate X) ∙ (comp-assoc (terminate X) x (id A)) ⁻¹) =₂
      (comp-unitˡ (const {P = X} x))
    constant-coordinate = cancel-right (comp-assoc (terminate X) x (id A))
        (comp-unitˡ (const x)) ∙
      isoComp-cong ((left-unitor-comp (terminate X) x) ⁻¹)
        (idIso ((comp-assoc (terminate X) x (id A)) ⁻¹))

    close-vertex : (vertex ∙ close) =₂
      (pair-cong (comp-unitˡ (id X)) (comp-unitˡ (const x)))
    close-vertex = pair-cong-Iso₂ (isoComp-unitˡ-at (comp-unitˡ (id X))) constant-coordinate ∙
      (pair-cong-comp (idIso (id X)) (comp-unitˡ (id X))
        (comp-unitˡ x ▷ terminate X) ((comp-assoc (terminate X) x (id A)) ⁻¹)) ⁻¹

    comparison : (vertex ∙ χ) =₂ (comp-unitˡ i ∙ (δ ▷ i))
    comparison = Universal.product-pair-unit 𝒯 M ℱ (id X) (const x) ∙
      (isoComp-cong close-vertex (idIso step) ∙
        (isoComp-assoc-at vertex close step) ⁻¹)

module At {A C : CAT} (x : Obj-abs A) where
  X = Fun A C
  e = funEval {C = A} {D = C}
  i = insert {X = X} x
  K = productMap (id X) (id A)
  χ = insertion X (id A) x
  δ = productMap-id X A
  β = funUncurry-id A C
  assoc = comp-assoc i K e
  vertex = evaluate-cong {C = C} (comp-unitˡ x)
  restriction = (e ◁ χ) ∙ assoc

  abstract
    product-image : (vertex ∙ (e ◁ χ)) =₂
      ((e ◁ comp-unitˡ i) ∙ (e ◁ (δ ▷ i)))
    product-image = postWhisker-isoComp-at e (comp-unitˡ i) (δ ▷ i) ∙
      ((postWhisker e ◁ Product.comparison X x) ∙
        (postWhisker-isoComp-at e (Product.vertex X x) χ) ⁻¹)

    normalize : (vertex ∙ restriction) =₂ (β ▷ i)
    normalize = isoComp-unitʳ-at (β ▷ i) ∙
      (isoComp-cong (idIso (β ▷ i)) (isoComp-inverseˡ-at assoc) ∙
      (isoComp-assoc-at (β ▷ i) (assoc ⁻¹) assoc ∙
      (isoComp-cong ((Universal.Universal.beta-slide 𝒯 M ℱ {C = C} x) ⁻¹) (idIso assoc) ∙
      (isoComp-cong product-image (idIso assoc) ∙
        (isoComp-assoc-at vertex (e ◁ χ) assoc) ⁻¹))))

    comparison : ((comp-unitʳ e ∙ (e ◁ δ)) ▷ i) =₂
      (evaluate-cong {C = C} (comp-unitˡ x) ∙
        ((e ◁ insertion X (id A) x) ∙ comp-assoc i K e))
    comparison = normalize ⁻¹
```
