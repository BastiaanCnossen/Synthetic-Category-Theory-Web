# Evaluating an associativity square

A coherent square between two associative substitution routes remains
coherent after evaluation and an identified evaluation functor. This is
an external scalar calculation using the pentagon and naturality.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedAssociativitySquare
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at; preWhisker-comp-at; postWhisker-comp-at)

module At {A B C D E : CAT} (t : MAP A B) (s : MAP B C) (p : MAP C D) (e : MAP D E)
  {H : MAP B D} {j : MAP A C} {P : MAP A D} {U : MAP C E}
  (δ : (p ∘ s) =₁ H) (α : (H ∘ t) =₁ P) (κ : (s ∘ t) =₁ j)
  (ψ : (p ∘ j) =₁ P) (β : U =₁ (e ∘ p))
  (square : (α ∙ (δ ▷ t)) =₂ (ψ ∙ ((p ◁ κ) ∙ comp-assoc t s p))) where
  aE = (e ◁ α) ∙ comp-assoc t H e
  dE = (e ◁ δ) ∙ (comp-assoc s p e ∙ (β ▷ s))
  nE = (e ◁ ψ) ∙ (comp-assoc j p e ∙ (β ▷ j))
  A₀ = comp-assoc t (p ∘ s) e
  A₁ = comp-assoc (s ∘ t) p e
  A₂ = comp-assoc j p e
  Atail = comp-assoc t s U
  btail = (β ▷ s) ▷ t
  right-tail = (U ◁ κ) ∙ Atail

  abstract
    head-slide : (aE ∙ ((e ◁ δ) ▷ t)) =₂ ((e ◁ (α ∙ (δ ▷ t))) ∙ A₀)
    head-slide = isoComp-cong ((postWhisker-isoComp-at e α (δ ▷ t)) ⁻¹) (idIso A₀) ∙
      (isoComp-assoc-at (e ◁ α) (e ◁ (δ ▷ t)) A₀) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ α)) (whisker-mixed-at δ t e) ∙
      isoComp-assoc-at (e ◁ α) (comp-assoc t H e) ((e ◁ δ) ▷ t)

    left-normal : (aE ∙ (dE ▷ t)) =₂
      ((e ◁ (α ∙ (δ ▷ t))) ∙ (A₀ ∙ ((comp-assoc s p e ▷ t) ∙ btail)))
    left-normal = isoComp-assoc-at (e ◁ (α ∙ (δ ▷ t))) A₀ ((comp-assoc s p e ▷ t) ∙ btail) ∙
      isoComp-cong head-slide (idIso ((comp-assoc s p e ▷ t) ∙ btail)) ∙
      (isoComp-assoc-at aE ((e ◁ δ) ▷ t) ((comp-assoc s p e ▷ t) ∙ btail)) ⁻¹ ∙
      isoComp-cong (idIso aE)
        (isoComp-cong (idIso ((e ◁ δ) ▷ t)) (preWhisker-isoComp-at (comp-assoc s p e) (β ▷ s) t) ∙
          preWhisker-isoComp-at (e ◁ δ) (comp-assoc s p e ∙ (β ▷ s)) t)

    beta-pentagon : ((e ◁ comp-assoc t s p) ∙ (A₀ ∙ ((comp-assoc s p e ▷ t) ∙ btail))) =₂
      (A₁ ∙ ((β ▷ (s ∘ t)) ∙ Atail))
    beta-pentagon = isoComp-cong (idIso A₁) (preWhisker-comp-at β s t) ∙
      isoComp-assoc-at A₁ (comp-assoc t s (e ∘ p)) btail ∙
      isoComp-cong ((pentagon-whiskered t s p e) ⁻¹) (idIso btail) ∙
      (isoComp-assoc-at (e ◁ comp-assoc t s p) (A₀ ∙ (comp-assoc s p e ▷ t)) btail) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ comp-assoc t s p))
        ((isoComp-assoc-at A₀ (comp-assoc s p e ▷ t) btail) ⁻¹)

    slide-beta : ((e ◁ (p ◁ κ)) ∙ (A₁ ∙ ((β ▷ (s ∘ t)) ∙ Atail))) =₂
      ((A₂ ∙ (β ▷ j)) ∙ right-tail)
    slide-beta = (isoComp-assoc-at A₂ (β ▷ j) right-tail) ⁻¹ ∙
      isoComp-cong (idIso A₂) (isoComp-assoc-at (β ▷ j) (U ◁ κ) Atail) ∙
      isoComp-cong (idIso A₂) (isoComp-cong ((interchange-at β κ) ⁻¹) (idIso Atail)) ∙
      isoComp-cong (idIso A₂) ((isoComp-assoc-at ((e ∘ p) ◁ κ) (β ▷ (s ∘ t)) Atail) ⁻¹) ∙
      isoComp-assoc-at A₂ ((e ∘ p) ◁ κ) ((β ▷ (s ∘ t)) ∙ Atail) ∙
      isoComp-cong ((postWhisker-comp-at κ p e) ⁻¹) (idIso ((β ▷ (s ∘ t)) ∙ Atail)) ∙
      (isoComp-assoc-at (e ◁ (p ◁ κ)) A₁ ((β ▷ (s ∘ t)) ∙ Atail)) ⁻¹

    product-image : (e ◁ (α ∙ (δ ▷ t))) =₂
      ((e ◁ ψ) ∙ ((e ◁ (p ◁ κ)) ∙ (e ◁ comp-assoc t s p)))
    product-image = isoComp-cong (idIso (e ◁ ψ)) (postWhisker-isoComp-at e (p ◁ κ) (comp-assoc t s p)) ∙
      postWhisker-isoComp-at e ψ ((p ◁ κ) ∙ comp-assoc t s p) ∙ (postWhisker e ◁ square)

    value : (aE ∙ (dE ▷ t)) =₂ (nE ∙ right-tail)
    value = (isoComp-assoc-at (e ◁ ψ) (A₂ ∙ (β ▷ j)) right-tail) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ ψ)) slide-beta ∙
      isoComp-cong (idIso (e ◁ ψ)) (isoComp-cong (idIso (e ◁ (p ◁ κ))) beta-pentagon) ∙
      isoComp-cong (idIso (e ◁ ψ))
        (isoComp-assoc-at (e ◁ (p ◁ κ)) (e ◁ comp-assoc t s p)
          (A₀ ∙ ((comp-assoc s p e ▷ t) ∙ btail))) ∙
      isoComp-assoc-at (e ◁ ψ) ((e ◁ (p ◁ κ)) ∙ (e ◁ comp-assoc t s p))
        (A₀ ∙ ((comp-assoc s p e ▷ t) ∙ btail)) ∙
      isoComp-cong product-image (idIso (A₀ ∙ ((comp-assoc s p e ▷ t) ∙ btail))) ∙ left-normal

    append : {V : MAP B E} (q : V =₁ (U ∘ s)) →
      (aE ∙ ((dE ∙ q) ▷ t)) =₂ (nE ∙ ((U ◁ κ) ∙ (Atail ∙ (q ▷ t))))
    append q = isoComp-cong (idIso nE) (isoComp-assoc-at (U ◁ κ) Atail (q ▷ t)) ∙
      isoComp-assoc-at nE right-tail (q ▷ t) ∙
      isoComp-cong value (idIso (q ▷ t)) ∙
      (isoComp-assoc-at aE (dE ▷ t) (q ▷ t)) ⁻¹ ∙
      isoComp-cong (idIso aE) (preWhisker-isoComp-at dE q t)
```
