# Pairing indexed functors and the product comparison

Pairing curries the pair of native evaluations. Its evaluation triangle,
projection comparisons and substitution law provide the constructions used
by the actual product comparison (`lem:FunctorCategoryIntoProduct`).

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.FunctorProducts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitʳ; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying
open import SCT.VolumeI.Chapter01.Section07.Functoriality

module _ {Γ : Context} {E C D : CAT Γ} where
  funPair : {T : CAT Γ} → MAP T (Fun E C) → MAP T (Fun E D) → MAP T (Fun E (C × D))
  funPair f g = funCurry {C = E} {D = C × D}
    (pair (funUncurry {C = E} {D = C} f) (funUncurry {C = E} {D = D} g))

  funPair-β : {T : CAT Γ} (f : MAP T (Fun E C)) (g : MAP T (Fun E D))
    → funUncurry {C = E} {D = C × D} (funPair f g) =₁
        pair (funUncurry {C = E} {D = C} f) (funUncurry {C = E} {D = D} g)
  funPair-β f g = funCurry-β {C = E} {D = C × D} _

  module _ {X T : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    funPair⁼ : {f f′ : MAP T (Fun E C)} {g g′ : MAP T (Fun E D)}
      → f ＝ f′ → g ＝ g′ → funPair f g ＝ funPair f′ g′
    funPair⁼ α β = curry⁼ (funEval {C = E} {D = C × D}) (funUniversal E (C × D))
      (pair⁼ (evaluate⁼ (funEval {C = E} {D = C}) α) (evaluate⁼ (funEval {C = E} {D = D}) β))

    funPair⁼-evaluation : {f f′ : MAP T (Fun E C)} {g g′ : MAP T (Fun E D)}
      (α : f ＝ f′) (β : g ＝ g′)
      → SquareCell₌ (evaluate⁼ (funEval {C = E} {D = C × D}) (funPair⁼ α β))
          (pair⁼ (evaluate⁼ (funEval {C = E} {D = C}) α) (evaluate⁼ (funEval {C = E} {D = D}) β))
          (const (funPair-β f g)) (const (funPair-β f′ g′))
    funPair⁼-evaluation α β = curry⁼-evaluation (funEval {C = E} {D = C × D})
      (funUniversal E (C × D)) _

  funPair-projection₁ : {T : CAT Γ} (f : MAP T (Fun E C)) (g : MAP T (Fun E D))
    → (funPost {C = E} pr₁ ∘ funPair f g) =₁ f
  funPair-projection₁ f g = reflect (funEval {C = E} {D = C}) (funUniversal E C) _ _
    (pair-β₁ (funUncurry {C = E} {D = C} f) (funUncurry {C = E} {D = D} g) ∙
      ((pr₁ ◁ funPair-β f g) ∙ funPost-uncurry pr₁ (funPair f g)))

  funPair-projection₂ : {T : CAT Γ} (f : MAP T (Fun E C)) (g : MAP T (Fun E D))
    → (funPost {C = E} pr₂ ∘ funPair f g) =₁ g
  funPair-projection₂ f g = reflect (funEval {C = E} {D = D}) (funUniversal E D) _ _
    (pair-β₂ (funUncurry {C = E} {D = C} f) (funUncurry {C = E} {D = D} g) ∙
      ((pr₂ ◁ funPair-β f g) ∙ funPost-uncurry pr₂ (funPair f g)))

  funPair-η : {T : CAT Γ} (h : MAP T (Fun E (C × D)))
    → funPair (funPost {C = E} pr₁ ∘ h) (funPost {C = E} pr₂ ∘ h) =₁ h
  funPair-η h = reflect (funEval {C = E} {D = C × D}) (funUniversal E (C × D)) _ _
    (pair-η (funUncurry {C = E} {D = C × D} h) ∙
      (pair⁼ (funPost-uncurry pr₁ h) (funPost-uncurry pr₂ h) ∙
        funPair-β (funPost {C = E} pr₁ ∘ h) (funPost {C = E} pr₂ ∘ h)))

  funPair-restrict : {R T : CAT Γ} (f : MAP T (Fun E C)) (g : MAP T (Fun E D)) (r : MAP R T)
    → (funPair f g ∘ r) =₁ funPair (f ∘ r) (g ∘ r)
  funPair-restrict f g r = reflect (funEval {C = E} {D = C × D}) (funUniversal E (C × D)) _ _
    ((funPair-β (f ∘ r) (g ∘ r)) ⁻¹ ∙
      (pair⁼ ((evaluate-restrict (funEval {C = E} {D = C}) f r) ⁻¹)
        ((evaluate-restrict (funEval {C = E} {D = D}) g r) ⁻¹) ∙
        (pair-pre (funUncurry {C = E} {D = C} f) (funUncurry {C = E} {D = D} g) (productMap r (id E)) ∙
          ((funPair-β f g ▷ productMap r (id E)) ∙
            evaluate-restrict (funEval {C = E} {D = C × D}) (funPair f g) r))))
```

## The actual product comparison

Its forward functor is the pair of the two specified postcomposition
functors. Pairing the two projections gives its chosen inverse. Projection,
substitution and eta prove both inverse laws.

```agda
module ProductComparison {Γ : Context} (E C D : CAT Γ) where
  Source = Fun E (C × D)
  Target = Fun E C × Fun E D
  private
    left : MAP Source (Fun E C)
    left = funPost {C = E} pr₁
    right : MAP Source (Fun E D)
    right = funPost {C = E} pr₂

  forward : MAP Source Target
  forward = pair left right
  backward : MAP Target Source
  backward = funPair {E = E} {C = C} {D = D} pr₁ pr₂

  forward-backward : (forward ∘ backward) =₁ id Target
  forward-backward = pair-projections ∙
    (pair⁼ (funPair-projection₁ pr₁ pr₂) (funPair-projection₂ pr₁ pr₂) ∙ pair-pre left right backward)

  backward-forward : (backward ∘ forward) =₁ id Source
  backward-forward = funPair-η (id Source) ∙
    (funPair⁼ ((comp-unitʳ left) ⁻¹ ∙ pair-β₁ left right)
      ((comp-unitʳ right) ⁻¹ ∙ pair-β₂ left right) ∙ funPair-restrict pr₁ pr₂ forward)

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward
    ; left-inverse-law = backward-forward ⁻¹
    ; right-inverse-law = forward-backward ⁻¹ }
```
