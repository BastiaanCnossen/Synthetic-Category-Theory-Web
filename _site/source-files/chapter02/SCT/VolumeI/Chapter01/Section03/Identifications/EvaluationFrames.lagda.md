# Evaluation routes and endpoint frames

A square of functors determines a comparison between two evaluation
routes. Its naturality transports the complete equations of endpoint
frames. The comparison retains the supplied square and both associators.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.EvaluationFrames where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; postWhisker-comp₌; interchange-fixedOuter)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (paste-square₌; inverse-square₌; unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (postWhisker-comp-One)
```

## The comparison and its frame equation

Naturality of the evaluation route follows from the given square and
the associator and interchange laws. Cancelling that route recovers
the projected equation of the original endpoint frames.

```agda
module _ {Γ : Context} where
  evaluation-route : {P U V C D : CAT Γ}
    (F : MAP C D) (e : MAP U C) (d : MAP V D) (K : MAP U V)
    (b : (d ∘ K) =₁ (F ∘ e)) (h : MAP P U)
    → (d ∘ (K ∘ h)) =₁ (F ∘ (e ∘ h))
  evaluation-route F e d K b h = comp-assoc h e F ∙ ((b ▷ h) ∙ (comp-assoc h K d) ⁻¹)

  abstract
    evaluation-route-square : {P U V C D : CAT Γ}
      (F : MAP C D) (e : MAP U C) (d : MAP V D) (K : MAP U V)
      (b : (d ∘ K) =₁ (F ∘ e)) {h k : MAP P U} (delta : h =₁ k)
      → SquareCell₌ (d ◁ (K ◁ delta)) (F ◁ (e ◁ delta))
          (evaluation-route F e d K b h) (evaluation-route F e d K b k)
    evaluation-route-square F e d K b delta = paste-square₌
      (paste-square₌ (inverse-square₌ (postWhisker-comp-One delta K d))
        (unconst-sides₌ (interchange-fixedOuter b delta)))
      (postWhisker-comp-One delta e F)

    reflect-evaluation-frame : {P U V C D : CAT Γ}
      (F : MAP C D) (e : MAP U C) (d : MAP V D) (K : MAP U V)
      (b : (d ∘ K) =₁ (F ∘ e)) {h k : MAP P U} {x : MAP P C}
      (p : (e ∘ h) =₁ x) (q : (e ∘ k) =₁ x)
      (delta : h =₁ k) (alpha : (K ∘ h) =₁ (K ∘ k))
      → (K ◁ delta) =₂ alpha
      → (((F ◁ q) ∙ evaluation-route F e d K b k) ∙ (d ◁ alpha)) =₂
          ((F ◁ p) ∙ evaluation-route F e d K b h)
      → (F ◁ (q ∙ (e ◁ delta))) =₂ (F ◁ p)
    reflect-evaluation-frame F e d K b {h} {k} p q delta alpha prescribed same =
      cancel-right rh
        (normalized ∙ ((comp₌-assoc (F ◁ q) rk changed) ⁻¹ ∙
          (comp₌-cong (id₌ (F ◁ q)) ((evaluation-route-square F e d K b delta) ⁻¹) ∙
            comp₌-assoc (F ◁ q) (F ◁ (e ◁ delta)) rh))) ∙
      postWhisker-comp₌ F q (e ◁ delta)
      where
        rh : (d ∘ (K ∘ h)) =₁ (F ∘ (e ∘ h))
        rh = evaluation-route F e d K b h
        rk : (d ∘ (K ∘ k)) =₁ (F ∘ (e ∘ k))
        rk = evaluation-route F e d K b k
        changed : (d ∘ (K ∘ h)) =₁ (d ∘ (K ∘ k))
        changed = d ◁ (K ◁ delta)
        normalized : (((F ◁ q) ∙ rk) ∙ changed) =₂ ((F ◁ p) ∙ rh)
        normalized = same ∙ comp₌-cong (id₌ ((F ◁ q) ∙ rk)) (postWhisker d ◁ prescribed)
```

