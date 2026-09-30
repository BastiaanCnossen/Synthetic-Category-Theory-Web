# Normalizing evaluated projection pairs

A specified normalization of a pair of projections commutes with the
chosen evaluation of the identity. This retains the product eta and
composition unit comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedProjectionNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M public
open import SCT.VolumeI.Chapter01.Section04.Substitution.RetainedIdentityParameterChange 𝒯 M using (pair-projections-pre)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-comp)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (triangle-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

module At {Γ A B C : CAT} {x x′ : MAP Γ A} {y y′ : MAP Γ B}
  (e : MAP (A × B) C) (p : x =₁ x′) (q : y =₁ y′) where
  s : MAP Γ (A × B)
  s = pair x y
  δ = pair-cong p q
  η : pair (pr₁ {A} {B}) pr₂ =₁ id (A × B)
  η = pair-projections
  product-frame = pair-cong (p ∙ pair-β₁ x y) (q ∙ pair-β₂ x y) ∙ pair-pre pr₁ pr₂ s
  T₀ = comp-unitʳ e ∙ (e ◁ η)
  scalar = comp-unitˡ s ∙ (η ▷ s)
  associator = comp-assoc s (pair pr₁ pr₂) e

  abstract
    pair-normal : product-frame =₂ (δ ∙ scalar)
    pair-normal = isoComp-cong (idIso δ) ((pair-projections-pre x y) ⁻¹) ∙
      isoComp-assoc-at δ (pair-cong (pair-β₁ x y) (pair-β₂ x y)) (pair-pre pr₁ pr₂ s) ∙
      isoComp-cong (pair-cong-comp p (pair-β₁ x y) q (pair-β₂ x y)) (idIso (pair-pre pr₁ pr₂ s))

    evaluation-unit : (T₀ ▷ s) =₂ ((e ◁ scalar) ∙ associator)
    evaluation-unit = isoComp-cong ((postWhisker-isoComp-at e (comp-unitˡ s) (η ▷ s)) ⁻¹) (idIso associator) ∙
      (isoComp-assoc-at (e ◁ comp-unitˡ s) (e ◁ (η ▷ s)) associator) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ comp-unitˡ s)) (whisker-mixed-at η s e) ∙
      isoComp-assoc-at (e ◁ comp-unitˡ s) (comp-assoc s (id (A × B)) e) ((e ◁ η) ▷ s) ∙
      isoComp-cong (triangle-whiskered s e) (idIso ((e ◁ η) ▷ s)) ∙
      preWhisker-isoComp-at (comp-unitʳ e) (e ◁ η) s

    value : ((e ◁ product-frame) ∙ associator) =₂ ((e ◁ δ) ∙ (T₀ ▷ s))
    value = isoComp-cong (idIso (e ◁ δ)) (evaluation-unit ⁻¹) ∙
      isoComp-assoc-at (e ◁ δ) (e ◁ scalar) associator ∙
      isoComp-cong (postWhisker-isoComp-at e δ scalar) (idIso associator) ∙
      isoComp-cong (postWhisker e ◁ pair-normal) (idIso associator)
```
