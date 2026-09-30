# Constant diagrams with their uncurrying computation

The chosen comparison for postcomposition of constant diagrams retains
its uncurried image. The comparison with a constant uncurried diagram is
natural in the entire parameter identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantDiagramNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyProductFunctor
  vocabulary terminal products productLaws composition vertical whiskering
  using (productFamily; productFamily-absolute; productFamily-cong)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence
  vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₁)

import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as ProductSubstitution
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.SubstitutionCoherence 𝒯 M ℱ
  using (funUncurry-restrict-iterated)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized
  using (module WhiskeringLaws)
open WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (preWhisker-comp-at)

module At (A : CAT) where
  comparison : {Γ C : CAT} (h : MAP Γ C) →
    funUncurry (constantDiagram A C ∘ h) =₁ (h ∘ pr₁)
  comparison h = pair-β₁ (h ∘ pr₁) (id A ∘ pr₂) ∙
    ((funCurry-β pr₁ ▷ productMap h (id A)) ∙ funUncurry-restrict (constantDiagram A _) h)

  module Naturality {Γ C : CAT} {h k : MAP Γ C} (γ : h =₁ k) where
    cC = constantDiagram A C
    R : MAP Γ C → MAP (Γ × A) (C × A)
    R t = productMap t (id A)
    δ = productMap-cong γ (idIso (id A))
    Θh = funUncurry-restrict cC h
    Θk = funUncurry-restrict cC k
    βh = funCurry-β (pr₁ {C = C} {D = A}) ▷ R h
    βk = funCurry-β (pr₁ {C = C} {D = A}) ▷ R k
    πh = pair-β₁ (h ∘ pr₁) (id A ∘ pr₂)
    πk = pair-β₁ (k ∘ pr₁) (id A ∘ pr₂)

    abstract
      product-action : productFamily γ (const (idIso (id A))) =₂ δ
      product-action = productFamily-absolute γ (idIso (id A)) ∙
        productFamily-cong (idIso γ) (const-One (idIso (id A)))

      substitution : (Θk ∙ funUncurryIso (cC ◁ γ)) =₂ ((funUncurry cC ◁ δ) ∙ Θh)
      substitution = isoComp-cong (postWhisker (funUncurry cC) ◁ product-action) (const-One Θh) ∙
        uncurry-restrict-substitution cC γ ∙
        (isoComp-cong (const-One Θk) (uncurryFamily-absolute (cC ◁ γ))) ⁻¹

      evaluation : (βk ∙ (funUncurry cC ◁ δ)) =₂ ((pr₁ ◁ δ) ∙ βh)
      evaluation = interchange-at (funCurry-β (pr₁ {C = C} {D = A})) δ

      projection : (πk ∙ (pr₁ ◁ δ)) =₂ ((γ ▷ pr₁) ∙ πh)
      projection = pair-cong-triangle₁ (γ ▷ pr₁) (idIso (id A) ▷ pr₂)

      value : (comparison k ∙ funUncurryIso (cC ◁ γ)) =₂ ((γ ▷ pr₁) ∙ comparison h)
      value = paste-squares (βh ∙ Θh) (βk ∙ Θk) πh πk
        (funUncurryIso (cC ◁ γ)) (pr₁ ◁ δ) (γ ▷ pr₁)
        (paste-squares Θh Θk βh βk (funUncurryIso (cC ◁ γ)) (funUncurry cC ◁ δ) (pr₁ ◁ δ)
          substitution evaluation) projection

  module Post {C D : CAT} (f : MAP C D) where
    left = constantDiagram A D ∘ f
    right = funPost f ∘ constantDiagram A C
    evaluated : funUncurry right =₁ (f ∘ pr₁)
    evaluated = (f ◁ funCurry-β pr₁) ∙ funPost-uncurry f (constantDiagram A C)
    raw : funUncurry left =₁ funUncurry right
    raw = evaluated ⁻¹ ∙ comparison f
    value : left =₁ right
    value = funIsoReflect left right raw
    computation : funUncurryIso value =₂ raw
    computation = funIsoReflect-β left right raw

  module CompositeParameter {Γ C D : CAT} (f : MAP C D) (h : MAP Γ C) where
    cD = constantDiagram A D
    module Coordinates = ProductSubstitution.Coordinates 𝒯 M A f h using (first; projection₁)
    R : {X Y : CAT} → MAP X Y → MAP (X × A) (Y × A)
    R k = productMap k (id A)
    κ = slice-comparison {C = A} f h
    β = funCurry-β (pr₁ {C = D} {D = A})
    πf = pair-β₁ (f ∘ pr₁) (id A ∘ pr₂)
    πfh = pair-β₁ ((f ∘ h) ∘ pr₁) (id A ∘ pr₂)
    assocU = comp-assoc (R h) (R f) (funUncurry cD)
    assocπ = comp-assoc (R h) (R f) pr₁
    Θf = funUncurry-restrict cD f
    Θh = funUncurry-restrict (cD ∘ f) h
    Θfh = funUncurry-restrict cD (f ∘ h)
    input = funUncurryIso (comp-assoc h f cD)
    tail = (Θf ▷ R h) ∙ Θh

    abstract
      projection : (πfh ∙ ((pr₁ ◁ κ) ∙ assocπ)) =₂
        (Coordinates.first ∙ (πf ▷ R h))
      projection = isoComp-cong (idIso Coordinates.first)
          (isoComp-unitʳ-at (πf ▷ R h) ∙
            (isoComp-cong (idIso (πf ▷ R h)) (isoComp-inverseˡ-at assocπ) ∙
              isoComp-assoc-at (πf ▷ R h) (assocπ ⁻¹) assocπ)) ∙
        (isoComp-assoc-at Coordinates.first ((πf ▷ R h) ∙ assocπ ⁻¹) assocπ ∙
        (isoComp-cong Coordinates.projection₁ (idIso assocπ) ∙
          (isoComp-assoc-at πfh (pr₁ ◁ κ) assocπ) ⁻¹))

      evaluation : ((β ▷ R (f ∘ h)) ∙ ((funUncurry cD ◁ κ) ∙ assocU)) =₂
        ((pr₁ ◁ κ) ∙ (assocπ ∙ ((β ▷ R f) ▷ R h)))
      evaluation = isoComp-cong (idIso (pr₁ ◁ κ)) (preWhisker-comp-at β (R f) (R h) ⁻¹) ∙
        (isoComp-assoc-at (pr₁ ◁ κ) (β ▷ (R f ∘ R h)) assocU ∙
        (isoComp-cong (interchange-at β κ) (idIso assocU) ∙
          (isoComp-assoc-at (β ▷ R (f ∘ h)) (funUncurry cD ◁ κ) assocU) ⁻¹))

      frame : (πfh ∙ ((β ▷ R (f ∘ h)) ∙ ((funUncurry cD ◁ κ) ∙ assocU))) =₂
        (Coordinates.first ∙ ((πf ∙ (β ▷ R f)) ▷ R h))
      frame = isoComp-cong (idIso Coordinates.first)
          (preWhisker-isoComp-at πf (β ▷ R f) (R h) ⁻¹) ∙
        (isoComp-assoc-at Coordinates.first (πf ▷ R h) ((β ▷ R f) ▷ R h) ∙
        (isoComp-cong projection (idIso ((β ▷ R f) ▷ R h)) ∙
        (isoComp-assoc-at πfh ((pr₁ ◁ κ) ∙ assocπ) ((β ▷ R f) ▷ R h) ⁻¹ ∙
        (isoComp-cong (idIso πfh)
          (isoComp-assoc-at (pr₁ ◁ κ) assocπ ((β ▷ R f) ▷ R h) ⁻¹) ∙
          isoComp-cong (idIso πfh) evaluation))))

      value : (comparison (f ∘ h) ∙ input) =₂
        (Coordinates.first ∙ ((comparison f ▷ R h) ∙ Θh))
      value = isoComp-cong (idIso Coordinates.first)
          (isoComp-cong
              ((preWhisker (R h) ◁ isoComp-assoc-at πf (β ▷ R f) Θf) ∙
                (preWhisker-isoComp-at (πf ∙ (β ▷ R f)) Θf (R h)) ⁻¹)
              (idIso Θh) ∙
            (isoComp-assoc-at ((πf ∙ (β ▷ R f)) ▷ R h) (Θf ▷ R h) Θh) ⁻¹) ∙
        (isoComp-assoc-at Coordinates.first ((πf ∙ (β ▷ R f)) ▷ R h) tail ∙
        (isoComp-cong frame (idIso tail) ∙
        (isoComp-assoc-at πfh ((β ▷ R (f ∘ h)) ∙ ((funUncurry cD ◁ κ) ∙ assocU)) tail ⁻¹ ∙
        (isoComp-cong (idIso πfh)
          (isoComp-assoc-at (β ▷ R (f ∘ h)) ((funUncurry cD ◁ κ) ∙ assocU) tail ⁻¹ ∙
            isoComp-cong (idIso (β ▷ R (f ∘ h)))
              (isoComp-assoc-at (funUncurry cD ◁ κ) assocU tail ⁻¹)) ∙
        (isoComp-cong (idIso πfh)
          (isoComp-cong (idIso (β ▷ R (f ∘ h))) (funUncurry-restrict-iterated cD f h)) ∙
        (isoComp-cong (idIso πfh)
          (isoComp-assoc-at (β ▷ R (f ∘ h)) Θfh input) ∙
          isoComp-assoc-at πfh ((β ▷ R (f ∘ h)) ∙ Θfh) input))))))
```
