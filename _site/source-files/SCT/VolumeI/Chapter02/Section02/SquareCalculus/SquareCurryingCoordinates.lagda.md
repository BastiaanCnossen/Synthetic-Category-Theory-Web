# Coordinates for currying a square

The outer arrow uses the second coordinate of the square. Thus the
coordinate map sends `((parameter, outer), inner)` to
`(parameter, (inner, outer))`. Its vertical and horizontal boundary
comparisons retain both product projection witnesses. Agreement of the
two orders of evaluating a corner remains a separate coherence claim.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
module PS = Projections 𝒯

coinsert : {A B : CAT} → Obj-abs A → MAP B (A × B)
coinsert {B = B} u = pair (const u) (id B)

module Coordinates (Γ A B : CAT) where
  parameter : MAP ((Γ × B) × A) Γ
  parameter = pr₁ ∘ pr₁
  inner : MAP ((Γ × B) × A) A
  inner = pr₂
  outer : MAP ((Γ × B) × A) B
  outer = pr₂ ∘ pr₁
  rectangle : MAP ((Γ × B) × A) (A × B)
  rectangle = pair inner outer

  permute : MAP ((Γ × B) × A) (Γ × (A × B))
  permute = pair parameter rectangle

  module Vertical (v : Obj-abs B) where
    step : MAP (Γ × A) ((Γ × B) × A)
    step = productMap (insert v) (id A)
    restriction : MAP (Γ × A) (Γ × (A × B))
    restriction = productMap (id Γ) (insert v)

    first-step : {D : CAT} (e : MAP (Γ × B) D) →
      ((e ∘ pr₁) ∘ step) =₁ ((e ∘ insert v) ∘ pr₁)
    first-step e = (comp-assoc pr₁ (insert v) e) ⁻¹ ∙
      ((e ◁ pair-β₁ (insert v ∘ pr₁) (id A ∘ pr₂)) ∙ comp-assoc step pr₁ e)

    parameter-step : (parameter ∘ step) =₁ pr₁
    parameter-step = comp-unitˡ pr₁ ∙ ((pair-β₁ (id Γ) (const v) ▷ pr₁) ∙ first-step pr₁)
    inner-step : (inner ∘ step) =₁ pr₂
    inner-step = comp-unitˡ pr₂ ∙ pair-β₂ (insert v ∘ pr₁) (id A ∘ pr₂)
    outer-step : (outer ∘ step) =₁ (const v)
    outer-step = const-pre v pr₁ ∙ ((pair-β₂ (id Γ) (const v) ▷ pr₁) ∙ first-step pr₂)
    rectangle-step : (rectangle ∘ step) =₁ (pair pr₂ (const v))
    rectangle-step = pair-cong inner-step outer-step ∙ pair-pre inner outer step

    source-first : (pr₁ ∘ (permute ∘ step)) =₁ pr₁
    source-first = PS.compose-base pr₁ permute (pair-β₁ parameter rectangle) step parameter-step
    source-second : (pr₂ ∘ (permute ∘ step)) =₁ (pair pr₂ (const v))
    source-second = PS.compose-base pr₂ permute (pair-β₂ parameter rectangle) step rectangle-step
    target-first : (pr₁ ∘ restriction) =₁ pr₁
    target-first = comp-unitˡ pr₁ ∙ pair-β₁ (id Γ ∘ pr₁) (insert v ∘ pr₂)
    target-second : (pr₂ ∘ restriction) =₁ (pair pr₂ (const v))
    target-second = (pair-cong (comp-unitˡ pr₂) (const-pre v pr₂) ∙
      pair-pre (id A) (const v) pr₂) ∙ pair-β₂ (id Γ ∘ pr₁) (insert v ∘ pr₂)
    first : (pr₁ ∘ (permute ∘ step)) =₁ (pr₁ ∘ restriction)
    first = target-first ⁻¹ ∙ source-first
    second : (pr₂ ∘ (permute ∘ step)) =₁ (pr₂ ∘ restriction)
    second = target-second ⁻¹ ∙ source-second

    comparison : (permute ∘ step) =₁ restriction
    comparison = pair-iso first second
    projection₁ : PS.Square pr₁ source-first target-first comparison
    projection₁ = cancel-inverse target-first source-first ∙
      isoComp-cong (idIso target-first) (pair-iso-β₁ first second)
    projection₂ : PS.Square pr₂ source-second target-second comparison
    projection₂ = cancel-inverse target-second source-second ∙
      isoComp-cong (idIso target-second) (pair-iso-β₂ first second)

  module Horizontal (u : Obj-abs A) where
    step : MAP (Γ × B) ((Γ × B) × A)
    step = insert u
    restriction : MAP (Γ × B) (Γ × (A × B))
    restriction = productMap (id Γ) (coinsert u)

    first-step : {D : CAT} (e : MAP (Γ × B) D) → ((e ∘ pr₁) ∘ step) =₁ e
    first-step e = comp-unitʳ e ∙ ((e ◁ pair-β₁ (id (Γ × B)) (const u)) ∙ comp-assoc step pr₁ e)
    rectangle-step : (rectangle ∘ step) =₁ (pair (const u) pr₂)
    rectangle-step = pair-cong (pair-β₂ (id (Γ × B)) (const u)) (first-step pr₂) ∙
      pair-pre inner outer step

    source-first : (pr₁ ∘ (permute ∘ step)) =₁ pr₁
    source-first = PS.compose-base pr₁ permute (pair-β₁ parameter rectangle) step (first-step pr₁)
    source-second : (pr₂ ∘ (permute ∘ step)) =₁ (pair (const u) pr₂)
    source-second = PS.compose-base pr₂ permute (pair-β₂ parameter rectangle) step rectangle-step
    target-first : (pr₁ ∘ restriction) =₁ pr₁
    target-first = comp-unitˡ pr₁ ∙ pair-β₁ (id Γ ∘ pr₁) (coinsert u ∘ pr₂)
    target-second : (pr₂ ∘ restriction) =₁ (pair (const u) pr₂)
    target-second = (pair-cong (const-pre u pr₂) (comp-unitˡ pr₂) ∙
      pair-pre (const u) (id B) pr₂) ∙ pair-β₂ (id Γ ∘ pr₁) (coinsert u ∘ pr₂)
    first : (pr₁ ∘ (permute ∘ step)) =₁ (pr₁ ∘ restriction)
    first = target-first ⁻¹ ∙ source-first
    second : (pr₂ ∘ (permute ∘ step)) =₁ (pr₂ ∘ restriction)
    second = target-second ⁻¹ ∙ source-second

    comparison : (permute ∘ step) =₁ restriction
    comparison = pair-iso first second
    projection₁ : PS.Square pr₁ source-first target-first comparison
    projection₁ = cancel-inverse target-first source-first ∙
      isoComp-cong (idIso target-first) (pair-iso-β₁ first second)
    projection₂ : PS.Square pr₂ source-second target-second comparison
    projection₂ = cancel-inverse target-second source-second ∙
      isoComp-cong (idIso target-second) (pair-iso-β₂ first second)
```
