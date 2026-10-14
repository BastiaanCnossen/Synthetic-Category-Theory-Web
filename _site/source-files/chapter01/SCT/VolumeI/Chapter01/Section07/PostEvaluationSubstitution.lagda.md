# Substitution of a represented postcomposition

A supplied evaluation triangle represents postcomposition. Its indexed
comparison is compatible with restriction, by the existing restriction
square for that triangle and compatibility of postcomposed triangles.
Specializing gives the literal substitution law of `funPost-uncurry`.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.PostEvaluationSubstitution where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (replace-sides₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport using (identification-restriction)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (postWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Functoriality

module RepresentedPostcomposition {Γ : Context} {F G K C D : CAT Γ}
  (e : MAP (F × K) C) (d : MAP (G × K) D) (H : MAP F G) (f : MAP C D)
  (β : evaluate d H =₁ (f ∘ e)) where
  private
    A = evaluate d H
    B = f ∘ e

    normal : {T : CAT Γ} (p : MAP T (F × K)) → (A ∘ p) =₁ (f ∘ (e ∘ p))
    normal p = comp-assoc p e f ∙ (β ▷ p)

    normal-frame : {Q R : CAT Γ} (p : MAP R (F × K)) (r : MAP Q R)
      (q : MAP Q (F × K)) (δ : (p ∘ r) =₁ q)
      → (normal q ∙ ((A ◁ δ) ∙ comp-assoc r p A)) =₂
          ((f ◁ post-triangle e p r δ) ∙ (comp-assoc r (e ∘ p) f ∙ (normal p ▷ r)))
    normal-frame p r q δ =
      comp₌-cong (id₌ image)
        (comp₌-cong (id₌ targetAssoc) ((preWhisker-comp₌ inputAssoc (β ▷ p) r) ⁻¹) ∙
          comp₌-assoc targetAssoc (inputAssoc ▷ r) doubleBeta) ∙
        (comp₌-assoc image (targetAssoc ∙ (inputAssoc ▷ r)) doubleBeta ∙
          (comp₌-cong (post-triangle-comp f e p r δ) (id₌ doubleBeta) ∙
            ((comp₌-assoc outputAssoc targetChange doubleBeta) ⁻¹ ∙
              (comp₌-cong (id₌ outputAssoc) (restriction-square ⁻¹) ∙
                comp₌-assoc outputAssoc (β ▷ q) sourceChange))))
      where
      inputAssoc = comp-assoc p e f
      outputAssoc = comp-assoc q e f
      targetAssoc = comp-assoc r (e ∘ p) f
      image = f ◁ post-triangle e p r δ
      sourceChange = (A ◁ δ) ∙ comp-assoc r p A
      targetChange = (B ◁ δ) ∙ comp-assoc r p B
      doubleBeta = (β ▷ p) ▷ r
      restriction-square : (targetChange ∙ doubleBeta) =₂ ((β ▷ q) ∙ sourceChange)
      restriction-square = replace-sides₌
        (comp₌-cong (id₌ (A ◁ δ)) (const-One (comp-assoc r p A)))
        (comp₌-cong (id₌ (B ◁ δ)) (const-One (comp-assoc r p B)))
        (identification-restriction β p r q δ)

  comparison : {T : CAT Γ} (g : MAP T F) → evaluate d (H ∘ g) =₁ (f ∘ evaluate e g)
  comparison g = normal (productMap g (id K)) ∙ evaluate-restrict d H g

  comparison-restrict : {R T : CAT Γ} (g : MAP T F) (r : MAP R T)
    → ((f ◁ evaluate-restrict e g r) ∙
        (comparison (g ∘ r) ∙ evaluate-cong d (comp-assoc r g H))) =₂
      (comp-assoc (productMap r (id K)) (evaluate e g) f ∙
        ((comparison g ▷ productMap r (id K)) ∙ evaluate-restrict d (H ∘ g) r))
  comparison-restrict g r =
    comp₌-cong (id₌ targetAssoc)
      (comp₌-cong ((preWhisker-comp₌ N U R) ⁻¹) (id₌ V) ∙ (comp₌-assoc (N ▷ R) (U ▷ R) V) ⁻¹) ∙
      (comp₌-assoc targetAssoc (N ▷ R) tail ∙
        (comp₌-cong cancelled (id₌ tail) ∙
          ((comp₌-assoc coefficient (NQ ∙ change) tail) ⁻¹ ∙
            (comp₌-cong (id₌ coefficient) ((comp₌-assoc NQ change tail) ⁻¹) ∙
              (comp₌-cong (id₌ coefficient)
                (comp₌-cong (id₌ NQ) iteration ∙ comp₌-assoc NQ W Z))))))
    where
    S = productMap g (id K)
    R = productMap r (id K)
    Q = productMap (g ∘ r) (id K)
    δ = productMap-first-comp g r
    N = normal S
    NQ = normal Q
    U = evaluate-restrict d H g
    V = evaluate-restrict d (H ∘ g) r
    W = evaluate-restrict d H (g ∘ r)
    Z = evaluate-cong d (comp-assoc r g H)
    coefficient = f ◁ evaluate-restrict e g r
    change = (A ◁ δ) ∙ comp-assoc R S A
    tail = (U ▷ R) ∙ V
    targetAssoc = comp-assoc R (evaluate e g) f
    iteration : (W ∙ Z) =₂ (change ∙ tail)
    iteration = (comp₌-assoc (A ◁ δ) (comp-assoc R S A) tail) ⁻¹ ∙ evaluate-restrict-assoc d H g r
    coefficient-normal : coefficient =₂ ((f ◁ evaluation-restriction-triangle e g r) ⁻¹)
    coefficient-normal = postWhisker-inverse f (evaluation-restriction-triangle e g r) ∙
      (postWhisker f ◁ evaluate-restrict-inverse-triangle e g r)
    cancelled : (coefficient ∙ (NQ ∙ change)) =₂ (targetAssoc ∙ (N ▷ R))
    cancelled = inv-comp-left (f ◁ evaluation-restriction-triangle e g r) (targetAssoc ∙ (N ▷ R)) ∙
      comp₌-cong coefficient-normal (normal-frame S R Q δ)

module _ {Γ : Context} {K C D T R : CAT Γ} (f : MAP C D) (g : MAP T (Fun K C)) (r : MAP R T) where
  private
    module Represented = RepresentedPostcomposition
      {F = Fun K C} {G = Fun K D} {K = K} {C = C} {D = D}
      (funEval {C = K} {D = C}) (funEval {C = K} {D = D}) (funPost {C = K} f) f (funPost-β {C = K} f)

    comparison-normalization : {Y : CAT Γ} (h : MAP Y (Fun K C))
      → Represented.comparison h =₂ funPost-uncurry {C = K} {D = C} {E = D} f h
    comparison-normalization h = comp₌-assoc
      (comp-assoc (productMap h (id K)) (funEval {C = K} {D = C}) f)
      (funPost-β {C = K} f ▷ productMap h (id K))
      (evaluate-restrict (funEval {C = K} {D = D}) (funPost {C = K} f) h)

  funPost-uncurry-restrict :
    ((f ◁ evaluate-restrict (funEval {C = K} {D = C}) g r) ∙
      (funPost-uncurry {C = K} {D = C} {E = D} f (g ∘ r) ∙
        evaluate-cong (funEval {C = K} {D = D}) (comp-assoc r g (funPost {C = K} f)))) =₂
    (comp-assoc (productMap r (id K)) (evaluate (funEval {C = K} {D = C}) g) f ∙
      ((funPost-uncurry {C = K} {D = C} {E = D} f g ▷ productMap r (id K)) ∙
        evaluate-restrict (funEval {C = K} {D = D}) (funPost {C = K} f ∘ g) r))
  funPost-uncurry-restrict =
    comp₌-cong (id₌ (comp-assoc (productMap r (id K)) (evaluate (funEval {C = K} {D = C}) g) f))
      (comp₌-cong (preWhisker (productMap r (id K)) ◁ comparison-normalization g)
        (id₌ (evaluate-restrict (funEval {C = K} {D = D}) (funPost {C = K} f ∘ g) r))) ∙
      (Represented.comparison-restrict g r ∙
        comp₌-cong (id₌ (f ◁ evaluate-restrict (funEval {C = K} {D = C}) g r))
          (comp₌-cong ((comparison-normalization (g ∘ r)) ⁻¹)
            (id₌ (evaluate-cong (funEval {C = K} {D = D}) (comp-assoc r g (funPost {C = K} f))))))
```
