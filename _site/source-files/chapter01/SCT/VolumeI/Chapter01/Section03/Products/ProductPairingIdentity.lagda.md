# Applying the identity product functor to a pair

The selected product-functor identity and the selected product-pair
comparison give the same identification of a pair with itself. This is
computed from the original projection triangles and Kelly's left-unit
law. It is the structural identity calculation needed by point evaluation.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.ProductPairingIdentity where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap; productMap-id)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (postWhisker-id-One; left-unitor-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-comp; pair⁼-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-pre-natural-inputs-One; pair-projections-pre)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)

private
  module _ {Γ : Context} where
    unit-post-triangle : {R K C : CAT Γ} (pi : MAP K C) (r : MAP R K)
      {x : MAP R C} (b : (pi ∘ r) =₁ x)
      → (comp-unitˡ x ∙ post-triangle (id C) pi r b) =₂
        (b ∙ (comp-unitˡ pi ▷ r))
    unit-post-triangle {C = C} pi r {x} b =
      comp₌-cong (id₌ b) (left-unitor-comp r pi) ∙
      (comp₌-assoc b (comp-unitˡ (pi ∘ r)) (comp-assoc r pi (id C)) ∙
      (comp₌-cong (postWhisker-id-One b) (id₌ (comp-assoc r pi (id C))) ∙
        (comp₌-assoc (comp-unitˡ x) (id C ◁ b) (comp-assoc r pi (id C))) ⁻¹))

module ProductPairingIdentity {Γ : Context} {P C D : CAT Γ}
  (u : MAP P C) (v : MAP P D) where
  private
    r : MAP P (C × D)
    r = pair u v
    beta₁ = pair-β₁ u v
    beta₂ = pair-β₂ u v
    first = post-triangle (id C) pr₁ r beta₁
    second = post-triangle (id D) pr₂ r beta₂
    before = pair-pre (id C ∘ pr₁) (id D ∘ pr₂) r
    after = pair-pre pr₁ pr₂ r
    l₁ = comp-unitˡ (pr₁ {C = C} {D = D})
    l₂ = comp-unitˡ (pr₂ {C = C} {D = D})
    unit-pair = pair⁼ l₁ l₂
    restricted-unit = pair⁼ (l₁ ▷ r) (l₂ ▷ r)
    paired-beta = pair⁼ beta₁ beta₂
    out = pair⁼ (comp-unitˡ u) (comp-unitˡ v)
    normalize₁ = (comp₌-assoc out (pair⁼ first second) before) ⁻¹
    normalize₂ = comp₌-cong
      ((pair⁼-comp (comp-unitˡ u) first (comp-unitˡ v) second) ⁻¹) (id₌ before)
    normalize₃ = comp₌-cong
      (pair⁼-cong (unit-post-triangle pr₁ r beta₁) (unit-post-triangle pr₂ r beta₂))
      (id₌ before)
    normalize₄ = comp₌-cong (pair⁼-comp beta₁ (l₁ ▷ r) beta₂ (l₂ ▷ r)) (id₌ before)
    normalize₅ = comp₌-assoc paired-beta restricted-unit before
    normalize₆ = comp₌-cong (id₌ paired-beta) ((pair-pre-natural-inputs-One l₁ l₂ r) ⁻¹)
    normalize₇ = (comp₌-assoc paired-beta after (unit-pair ▷ r)) ⁻¹
    normalize₈ = comp₌-cong ((pair-projections-pre u v) ⁻¹) (id₌ (unit-pair ▷ r))
    normalize₉ = comp₌-assoc (comp-unitˡ r) (pair-projections ▷ r) (unit-pair ▷ r)
    normalize₁₀ = comp₌-cong (id₌ (comp-unitˡ r))
      ((preWhisker-comp₌ pair-projections unit-pair r) ⁻¹)

  compatibility :
    (pair⁼ (comp-unitˡ u) (comp-unitˡ v) ∙ productMap-pair (id C) (id D) u v) =₂
    (comp-unitˡ (pair u v) ∙ (productMap-id C D ▷ pair u v))
  compatibility = normalize₁₀ ∙ (normalize₉ ∙ (normalize₈ ∙ (normalize₇ ∙
    (normalize₆ ∙ (normalize₅ ∙ (normalize₄ ∙ (normalize₃ ∙ (normalize₂ ∙ normalize₁))))))))
```
