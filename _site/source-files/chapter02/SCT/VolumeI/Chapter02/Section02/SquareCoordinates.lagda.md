# Coordinates of a parametrized square

The outer arrow follows the second coordinate. The coordinate map sends
((parameter, outer), inner) to (parameter, (inner, outer)). Restricting either
coordinate gives the corresponding side of the square. Each comparison
retains both of its product projection equations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCoordinates where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; comp-inv-left; const-pre)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (CompatibleOver; compose-triangle)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert)

module _ {Γ : Context} where
  coinsert : MAP One ([1] {Γ = Γ}) → MAP [1] ([1] × [1])
  coinsert u = pair (const u) (id [1])

module SquareCoordinates {Γ : Context} (P : CAT Γ) where
  private
    I = [1] {Γ = Γ}
  parameter : MAP ((P × I) × I) P
  parameter = pr₁ ∘ pr₁
  inner : MAP ((P × I) × I) I
  inner = pr₂
  outer : MAP ((P × I) × I) I
  outer = pr₂ ∘ pr₁
  rectangle : MAP ((P × I) × I) (I × I)
  rectangle = pair inner outer
  permute : MAP ((P × I) × I) (P × (I × I))
  permute = pair parameter rectangle

  module Vertical (v : MAP One I) where
    step : MAP (P × I) ((P × I) × I)
    step = productMap (insert {P = P} v) (id I)
    restriction : MAP (P × I) (P × (I × I))
    restriction = productMap (id P) (insert {P = I} v)
    private
      first-step : {D : CAT Γ} (e : MAP (P × I) D)
        → ((e ∘ pr₁) ∘ step) =₁ ((e ∘ insert v) ∘ pr₁)
      first-step e = (comp-assoc pr₁ (insert v) e) ⁻¹ ∙
        ((e ◁ pair-β₁ (insert v ∘ pr₁) (id I ∘ pr₂)) ∙ comp-assoc step pr₁ e)
      parameter-step : (parameter ∘ step) =₁ pr₁
      parameter-step = comp-unitˡ pr₁ ∙ ((pair-β₁ (id P) (const v) ▷ pr₁) ∙ first-step pr₁)
      inner-step : (inner ∘ step) =₁ pr₂
      inner-step = comp-unitˡ pr₂ ∙ pair-β₂ (insert v ∘ pr₁) (id I ∘ pr₂)
      outer-step : (outer ∘ step) =₁ const v
      outer-step = const-pre v pr₁ ∙ ((pair-β₂ (id P) (const v) ▷ pr₁) ∙ first-step pr₂)
      rectangle-step : (rectangle ∘ step) =₁ pair pr₂ (const v)
      rectangle-step = pair⁼ inner-step outer-step ∙ pair-pre inner outer step
    source-first : (pr₁ ∘ (permute ∘ step)) =₁ pr₁
    source-first = compose-triangle pr₁ permute (pair-β₁ parameter rectangle) step parameter-step
    source-second : (pr₂ ∘ (permute ∘ step)) =₁ pair pr₂ (const v)
    source-second = compose-triangle pr₂ permute (pair-β₂ parameter rectangle) step rectangle-step
    target-first : (pr₁ ∘ restriction) =₁ pr₁
    target-first = comp-unitˡ pr₁ ∙ pair-β₁ (id P ∘ pr₁) (insert v ∘ pr₂)
    target-second : (pr₂ ∘ restriction) =₁ pair pr₂ (const v)
    target-second = (pair⁼ (comp-unitˡ pr₂) (const-pre v pr₂) ∙
      pair-pre (id I) (const v) pr₂) ∙ pair-β₂ (id P ∘ pr₁) (insert v ∘ pr₂)
    private
      first = target-first ⁻¹ ∙ source-first
      second = target-second ⁻¹ ∙ source-second
    comparison : (permute ∘ step) =₁ restriction
    comparison = pair₌ first second
    projection₁ : CompatibleOver pr₁ source-first target-first comparison
    projection₁ = comp-inv-left target-first source-first ∙ comp₌-cong (id₌ target-first) (pair₌-β₁ first second)
    projection₂ : CompatibleOver pr₂ source-second target-second comparison
    projection₂ = comp-inv-left target-second source-second ∙ comp₌-cong (id₌ target-second) (pair₌-β₂ first second)

  module Horizontal (u : MAP One I) where
    step : MAP (P × I) ((P × I) × I)
    step = insert u
    restriction : MAP (P × I) (P × (I × I))
    restriction = productMap (id P) (coinsert u)
    private
      first-step : {D : CAT Γ} (e : MAP (P × I) D) → ((e ∘ pr₁) ∘ step) =₁ e
      first-step e = comp-unitʳ e ∙ ((e ◁ pair-β₁ (id (P × I)) (const u)) ∙ comp-assoc step pr₁ e)
      rectangle-step : (rectangle ∘ step) =₁ pair (const u) pr₂
      rectangle-step = pair⁼ (pair-β₂ (id (P × I)) (const u)) (first-step pr₂) ∙
        pair-pre inner outer step
    source-first : (pr₁ ∘ (permute ∘ step)) =₁ pr₁
    source-first = compose-triangle pr₁ permute (pair-β₁ parameter rectangle) step (first-step pr₁)
    source-second : (pr₂ ∘ (permute ∘ step)) =₁ pair (const u) pr₂
    source-second = compose-triangle pr₂ permute (pair-β₂ parameter rectangle) step rectangle-step
    target-first : (pr₁ ∘ restriction) =₁ pr₁
    target-first = comp-unitˡ pr₁ ∙ pair-β₁ (id P ∘ pr₁) (coinsert u ∘ pr₂)
    target-second : (pr₂ ∘ restriction) =₁ pair (const u) pr₂
    target-second = (pair⁼ (const-pre u pr₂) (comp-unitˡ pr₂) ∙
      pair-pre (const u) (id I) pr₂) ∙ pair-β₂ (id P ∘ pr₁) (coinsert u ∘ pr₂)
    private
      first = target-first ⁻¹ ∙ source-first
      second = target-second ⁻¹ ∙ source-second
    comparison : (permute ∘ step) =₁ restriction
    comparison = pair₌ first second
    projection₁ : CompatibleOver pr₁ source-first target-first comparison
    projection₁ = comp-inv-left target-first source-first ∙ comp₌-cong (id₌ target-first) (pair₌-β₁ first second)
    projection₂ : CompatibleOver pr₂ source-second target-second comparison
    projection₂ = comp-inv-left target-second source-second ∙ comp₌-cong (id₌ target-second) (pair₌-β₂ first second)
```
