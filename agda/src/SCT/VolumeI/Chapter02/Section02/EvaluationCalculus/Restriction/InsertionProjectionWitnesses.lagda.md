# Projection witnesses for inserting an object

The comparison `insert-natural h x` is a quotient of two comparisons with
`pair h (const x)`. We retain both projection witnesses of that quotient.
These are equations for the existing insertion comparison, rather than a
replacement chosen merely to have the same endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductPairingComparisons as ProductPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionProjectionWitnesses
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open ProductPairing 𝒯 M using (quotient-projection; identity-coordinate)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)

module Parameter {X Y A : CAT} (h : MAP X Y) (x : Obj-abs A) where
  module Output = ProductPairing.ProductPair 𝒯 M h (id A) (id X) (const x)
    (comp-unitʳ h) (comp-unitˡ (const x))

  incoming = pair-cong (comp-unitˡ h) (const-pre x h) ∙ pair-pre (id Y) (const x) h
  outgoing = Output.comparison

  incoming₁ = comp-unitˡ h ∙ ((pair-β₁ (id Y) (const x) ▷ h) ∙
    (comp-assoc h (insert x) pr₁) ⁻¹)
  incoming₂ = const-pre x h ∙ ((pair-β₂ (id Y) (const x) ▷ h) ∙
    (comp-assoc h (insert x) pr₂) ⁻¹)
  outgoing₁ = Output.first ∙ ((pair-β₁ (h ∘ pr₁) (id A ∘ pr₂) ▷ insert x) ∙
    (comp-assoc (insert x) (productMap h (id A)) pr₁) ⁻¹)
  outgoing₂ = Output.second ∙ ((pair-β₂ (h ∘ pr₁) (id A ∘ pr₂) ▷ insert x) ∙
    (comp-assoc (insert x) (productMap h (id A)) pr₂) ⁻¹)

  normalized-outgoing₂ = pair-β₂ (id X) (const x) ∙
    (((comp-unitˡ pr₂ ∙ pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)) ▷ insert x) ∙
      (comp-assoc (insert x) (productMap h (id A)) pr₂) ⁻¹)

  abstract
    normalize-outgoing₂ : outgoing₂ =₂ normalized-outgoing₂
    normalize-outgoing₂ = isoComp-cong (idIso (pair-β₂ (id X) (const x)))
        (isoComp-cong ((preWhisker-isoComp-at (comp-unitˡ pr₂)
          (pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)) (insert x)) ⁻¹) (idIso _)) ∙
      (isoComp-cong (idIso (pair-β₂ (id X) (const x)))
        ((isoComp-assoc-at (comp-unitˡ pr₂ ▷ insert x)
          (pair-β₂ (h ∘ pr₁) (id A ∘ pr₂) ▷ insert x) _) ⁻¹) ∙
      (isoComp-assoc-at (pair-β₂ (id X) (const x)) (comp-unitˡ pr₂ ▷ insert x) _ ∙
        isoComp-cong (identity-coordinate pr₂ (insert x) (pair-β₂ (id X) (const x))) (idIso _)))

    projection₁ : (outgoing₁ ∙ (pr₁ ◁ insert-natural h x)) =₂ incoming₁
    projection₁ = quotient-projection pr₁ incoming₁ outgoing₁ (pair-β₁ h (const x))
      incoming outgoing
      (pair-pre-cong-triangle₁ (id Y) (const x) h (comp-unitˡ h) (const-pre x h))
      Output.projection₁

    projection₂ : (outgoing₂ ∙ (pr₂ ◁ insert-natural h x)) =₂ incoming₂
    projection₂ = quotient-projection pr₂ incoming₂ outgoing₂ (pair-β₂ h (const x))
      incoming outgoing
      (pair-pre-cong-triangle₂ (id Y) (const x) h (comp-unitˡ h) (const-pre x h))
      Output.projection₂

    normalized-projection₂ : (normalized-outgoing₂ ∙ (pr₂ ◁ insert-natural h x)) =₂ incoming₂
    normalized-projection₂ = projection₂ ∙
      isoComp-cong (normalize-outgoing₂ ⁻¹) (idIso (pr₂ ◁ insert-natural h x))
```
