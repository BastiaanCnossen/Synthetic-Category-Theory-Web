# Identifications and endpoint frames in products

A joint equivalence lifts two component identifications with both images
prescribed. Product coordinates assemble an endpoint frame with its two
projection equations. These constructions apply to ordinary functors and
identifications over an arbitrary categorical parameter.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.FramedComparisons where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section01.Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; comp-inv-left; inv-comp-right)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.Equivalences using (paired-postWhisker-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.Factorizations using (Factorization; factor-through-equiv; factor; triangle)
```

## Prescribed images through a joint equivalence

Factor the paired component identifications through the joint
postwhiskering equivalence. The chosen lift comes with both prescribed
image equations.

```agda
module _ {Γ : Context} where
  lift-paired-identifications : {P U V W : CAT Γ}
    (F : MAP U V) (G : MAP U W) (e : IsEquiv (pair F G))
    (h k : MAP P U) (alpha : (F ∘ h) =₁ (F ∘ k)) (beta : (G ∘ h) =₁ (G ∘ k))
    → h =₁ k
  lift-paired-identifications F G e h k alpha beta =
    factor (factor-through-equiv (paired-postWhisker-isEquiv F G e h k) (pair alpha beta))

  record JointIdentificationImages {P U V W : CAT Γ}
    (F : MAP U V) (G : MAP U W) {h k : MAP P U}
    (alpha : (F ∘ h) =₁ (F ∘ k)) (beta : (G ∘ h) =₁ (G ∘ k))
    (delta : h =₁ k) : Set m where
    field
      first : (F ◁ delta) =₂ alpha
      second : (G ◁ delta) =₂ beta

  abstract
    lift-paired-images : {P U V W : CAT Γ}
      (F : MAP U V) (G : MAP U W) (e : IsEquiv (pair F G))
      (h k : MAP P U) (alpha : (F ∘ h) =₁ (F ∘ k)) (beta : (G ∘ h) =₁ (G ∘ k))
      → JointIdentificationImages F G alpha beta (lift-paired-identifications F G e h k alpha beta)
    lift-paired-images F G e h k alpha beta = record
      { first = pair-β₁ alpha beta ∙ ((pr₁ ◁ triangle chosen) ∙
          (restrict-triangle pr₁ J (pair-β₁ (postWhisker F) (postWhisker G)) delta) ⁻¹)
      ; second = pair-β₂ alpha beta ∙ ((pr₂ ◁ triangle chosen) ∙
          (restrict-triangle pr₂ J (pair-β₂ (postWhisker F) (postWhisker G)) delta) ⁻¹) }
      where
        J : MAP (Equal h k) (Equal (F ∘ h) (F ∘ k) × Equal (G ∘ h) (G ∘ k))
        J = pair (postWhisker F) (postWhisker G)
        chosen : Factorization J (pair alpha beta)
        chosen = factor-through-equiv (paired-postWhisker-isEquiv F G e h k) (pair alpha beta)
        delta : h =₁ k
        delta = lift-paired-identifications F G e h k alpha beta
```

## Endpoint frames from their product coordinates

The two component routes determine a frame into the product together with
both projection equations, retaining the supplied endpoint identifications.

```agda
module _ {Γ : Context} where
  product-endpoint-frame : {P C D : CAT Γ} (u : MAP P (C × D)) (x : MAP P C) (y : MAP P D)
    {w₁ : MAP P C} {w₂ : MAP P D}
    (r₁ : w₁ =₁ (pr₁ ∘ u)) (r₂ : w₂ =₁ (pr₂ ∘ u))
    (p : w₁ =₁ x) (q : w₂ =₁ y) → u =₁ pair x y
  product-endpoint-frame u x y r₁ r₂ p q = pair₌
    ((pair-β₁ x y) ⁻¹ ∙ (p ∙ r₁ ⁻¹)) ((pair-β₂ x y) ⁻¹ ∙ (q ∙ r₂ ⁻¹))

  record ProductEndpointImages {P C D : CAT Γ}
    (u : MAP P (C × D)) (x : MAP P C) (y : MAP P D)
    {w₁ : MAP P C} {w₂ : MAP P D}
    (r₁ : w₁ =₁ (pr₁ ∘ u)) (r₂ : w₂ =₁ (pr₂ ∘ u))
    (p : w₁ =₁ x) (q : w₂ =₁ y) (frame : u =₁ pair x y) : Set m where
    field
      first : (pair-β₁ x y ∙ ((pr₁ ◁ frame) ∙ r₁)) =₂ p
      second : (pair-β₂ x y ∙ ((pr₂ ◁ frame) ∙ r₂)) =₂ q

  private
    normalize-coordinate : {P C D E : CAT Γ} (pi : MAP (C × D) E)
      {u v : MAP P (C × D)} {w z : MAP P E} (frame : u =₁ v)
      (b : (pi ∘ v) =₁ z) (r : w =₁ (pi ∘ u)) (p : w =₁ z)
      → (pi ◁ frame) =₂ (b ⁻¹ ∙ (p ∙ r ⁻¹))
      → (b ∙ ((pi ◁ frame) ∙ r)) =₂ p
    normalize-coordinate pi frame b r p image = inv-comp-right p r ∙
      (comp₌-cong (comp-inv-left b (p ∙ r ⁻¹) ∙ comp₌-cong (id₌ b) image) (id₌ r) ∙
        (comp₌-assoc b (pi ◁ frame) r) ⁻¹)

  abstract
    product-endpoint-images : {P C D : CAT Γ}
      (u : MAP P (C × D)) (x : MAP P C) (y : MAP P D)
      {w₁ : MAP P C} {w₂ : MAP P D}
      (r₁ : w₁ =₁ (pr₁ ∘ u)) (r₂ : w₂ =₁ (pr₂ ∘ u))
      (p : w₁ =₁ x) (q : w₂ =₁ y)
      → ProductEndpointImages u x y r₁ r₂ p q (product-endpoint-frame u x y r₁ r₂ p q)
    product-endpoint-images u x y r₁ r₂ p q = record
      { first = normalize-coordinate pr₁ frame (pair-β₁ x y) r₁ p (pair₌-β₁ first second)
      ; second = normalize-coordinate pr₂ frame (pair-β₂ x y) r₂ q (pair₌-β₂ first second) }
      where
        first : (pr₁ ∘ u) =₁ (pr₁ ∘ pair x y)
        first = (pair-β₁ x y) ⁻¹ ∙ (p ∙ r₁ ⁻¹)
        second : (pr₂ ∘ u) =₁ (pr₂ ∘ pair x y)
        second = (pair-β₂ x y) ⁻¹ ∙ (q ∙ r₂ ⁻¹)
        frame : u =₁ pair x y
        frame = product-endpoint-frame u x y r₁ r₂ p q
```

