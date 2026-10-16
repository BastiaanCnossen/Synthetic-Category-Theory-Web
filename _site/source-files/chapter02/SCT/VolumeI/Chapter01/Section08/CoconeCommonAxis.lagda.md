# A complete cocone comparison along a common axis

A full comparison of cocones transports both restrictions along a shared
axis. The common-axis triangle and the original target matching retain the
chosen paths. Removing the target endpoint frames gives a comparison of
the two selected restriction routes.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section08.CoconeCommonAxis where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp-inv-left)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-inverseʳ-One; cancel-left)
open import SCT.VolumeI.Chapter01.Section08.Cocones using (Cocone; CoconeIdentification₁)

module Comparison {Γ : Context} {A B D C : CAT Γ}
  {u : MAP A B} {l : MAP A D} {s t : Cocone u l C}
  (given : CoconeIdentification₁ s t)
  {z e x y : MAP A C}
  (first-axis : (Cocone.left s ∘ u) =₁ z)
  (second-axis : (Cocone.right s ∘ l) =₁ z)
  (axis-triangle : (second-axis ∙ Cocone.match s) =₂ first-axis)
  (source-frame : e =₁ z)
  (first-frame : x =₁ (Cocone.left t ∘ u))
  (second-frame : y =₁ (Cocone.right t ∘ l))
  (matching : x =₁ y)
  (matching-image : Cocone.match t =₂ (second-frame ∙ (matching ∙ first-frame ⁻¹))) where

  first-leg : (Cocone.left s ∘ u) =₁ (Cocone.left t ∘ u)
  first-leg = CoconeIdentification₁.left given ▷ u
  second-leg : (Cocone.right s ∘ l) =₁ (Cocone.right t ∘ l)
  second-leg = CoconeIdentification₁.right given ▷ l

  first-tail : e =₁ (Cocone.left s ∘ u)
  first-tail = first-axis ⁻¹ ∙ source-frame
  second-tail : e =₁ (Cocone.right s ∘ l)
  second-tail = second-axis ⁻¹ ∙ source-frame

  first-restriction : e =₁ (Cocone.left t ∘ u)
  first-restriction = first-leg ∙ first-tail
  second-restriction : e =₁ (Cocone.right t ∘ l)
  second-restriction = second-leg ∙ second-tail

  upper : e =₁ x
  upper = first-frame ⁻¹ ∙ first-restriction
  lower : e =₁ y
  lower = second-frame ⁻¹ ∙ second-restriction

  private
    source-matching = Cocone.match s
    restored-matching = second-frame ∙ (matching ∙ first-frame ⁻¹)

    axis-backward : (source-matching ∙ first-axis ⁻¹) =₂ second-axis ⁻¹
    axis-backward = cancel-left second-axis
      ((comp₌-inverseʳ-One second-axis) ⁻¹ ∙
        (comp₌-inverseʳ-One first-axis ∙
          (comp₌-cong axis-triangle (id₌ (first-axis ⁻¹)) ∙
            (comp₌-assoc second-axis source-matching (first-axis ⁻¹)) ⁻¹)))

    matching-square : (restored-matching ∙ first-leg) =₂ (second-leg ∙ source-matching)
    matching-square = CoconeIdentification₁.compatible given ∙
      comp₌-cong (matching-image ⁻¹) (id₌ first-leg)

    beta-word : (restored-matching ∙ first-restriction) =₂ second-restriction
    beta-word = comp₌-cong (id₌ second-leg)
        (comp₌-cong axis-backward (id₌ source-frame) ∙
          (comp₌-assoc source-matching (first-axis ⁻¹) source-frame) ⁻¹) ∙
      (comp₌-assoc second-leg source-matching first-tail ∙
        (comp₌-cong matching-square (id₌ first-tail) ∙
          (comp₌-assoc restored-matching first-leg first-tail) ⁻¹))

    restore-upper : (second-frame ∙ (matching ∙ upper)) =₂
      (restored-matching ∙ first-restriction)
    restore-upper = (comp₌-assoc second-frame
        (matching ∙ first-frame ⁻¹) first-restriction) ⁻¹ ∙
      comp₌-cong (id₌ second-frame)
        ((comp₌-assoc matching (first-frame ⁻¹) first-restriction) ⁻¹)

  abstract
    diagonal : (matching ∙ upper) =₂ lower
    diagonal = cancel-left second-frame
      ((comp-inv-left second-frame second-restriction) ⁻¹ ∙
        (beta-word ∙ restore-upper))
```
