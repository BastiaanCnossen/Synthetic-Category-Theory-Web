# Endpoint evaluation of the constant restriction

The constant restriction is compared with the actual constant family by
its chosen product comparison. The endpoint equation below agrees with
the existing `identity-boundary`, including its parameter projection.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.ConstantRestrictionCoordinates as Coordinates
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertions as Restriction
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.PairSectionEvaluation as PairSection
import SCT.VolumeI.Chapter01.Section04.Substitution.SectionComparisonEvaluation as Section
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.ConstantRestrictionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)

module Product {A B : CAT} (X : CAT) (x : Obj-abs A) (z : Obj-abs B) where
  module Coords = Coordinates.At 𝒯 M ℱ X x z
  open Coords using (π; ρ; i; t; s; b₁; point; constant-comparison)
  j = insert {X = X} z
  K = productMap (id X) (const {P = A} z)
  input = pair-cong (idIso (id X ∘ π)) constant-comparison
  comparison-to-constant = (pair-pre (id X) (const {P = X} z) π) ⁻¹ ∙ input
  vertex = pair-cong (idIso (id X)) (point ▷ t)
  χ = Restriction.insertion 𝒯 M ℱ X (const {P = A} z) x
  module Insert = Restriction.At 𝒯 M ℱ X (const {P = A} z) x
  step = pair-pre (id X ∘ π) (const {P = A} z ∘ ρ) i
  module Compared = PairSection.ComparedInputs 𝒯 π i b₁ (id X) (const {P = X} z)
    (idIso (id X ∘ π)) constant-comparison

  abstract
    right-normalization : (vertex ∙ χ) =₂
      (pair-cong Insert.first Coords.right-second ∙ step)
    right-normalization = isoComp-cong
        (pair-cong-Iso₂ (isoComp-unitˡ-at Insert.first) (idIso Coords.right-second) ∙
          (pair-cong-comp (idIso (id X)) Insert.first (point ▷ t) Insert.second) ⁻¹)
        (idIso step) ∙
      ((isoComp-assoc-at vertex (pair-cong Insert.first Insert.second) step) ⁻¹ ∙
        isoComp-cong (idIso vertex) Insert.normalization)

    comparison :
      (section-image π i b₁ j ∙ (comparison-to-constant ▷ i)) =₂ (vertex ∙ χ)
    comparison = right-normalization ⁻¹ ∙
      (isoComp-cong (pair-cong-Iso₂ Coords.first-coordinate Coords.second-coordinate)
        (idIso step) ∙ Compared.comparison)

module At {A B C : CAT} (x : Obj-abs A) (z : Obj-abs B) where
  X = Fun B C
  module Products = Product X x z
  module Coords = Coordinates.At 𝒯 M ℱ X x z
  e = funEval {C = B} {D = C}
  open Products using (j; K; comparison-to-constant; χ; vertex)
  open Coords using (π; i; b₁; point)

  constant-evaluation : (e ∘ K) =₁ (evaluate {C = C} z ∘ π)
  constant-evaluation = (comp-assoc π j e) ⁻¹ ∙ (e ◁ comparison-to-constant)

  abstract
    comparison :
      (section-image π i b₁ (evaluate {C = C} z) ∙ (constant-evaluation ▷ i)) =₂
      (evaluate-cong {C = C} point ∙ ((e ◁ χ) ∙ comp-assoc i K e))
    comparison = isoComp-assoc-at (e ◁ vertex) (e ◁ χ) (comp-assoc i K e) ∙
      (isoComp-cong (postWhisker-isoComp-at e vertex χ ∙
        (postWhisker e ◁ Products.comparison)) (idIso (comp-assoc i K e)) ∙
      Section.At.comparison 𝒯 π i b₁ j K comparison-to-constant e)
```
