# Iterated native evaluation

The existing first-factor product comparison is compatible with successive
substitutions. Postcomposing that restriction diagram with a supplied
evaluation proves compatibility of its native triangles. Inverting these
triangles recovers the literal chosen `evaluate-restrict` law, so clients
can use successive evaluation without rebuilding its coordinate proof.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution using (productMap-first-comp-assoc)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
  using (restriction-diagram; evaluation; post-compatible)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport using (square-to-changeEndpoints)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (inverse-composite; postWhisker-inverse; preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; comp₌-assoc; inv-comp-left)
open import SCT.VolumeI.Chapter01.Section07.Evaluation

module _ {Γ : Context} {F K D : CAT Γ} (e : MAP (F × K) D) where
  evaluation-restriction-triangle : {R T : CAT Γ} (g : MAP T F) (r : MAP R T)
    → (evaluate e g ∘ productMap r (id K)) =₁ evaluate e (g ∘ r)
  evaluation-restriction-triangle g r = post-triangle e (productMap g (id K)) (productMap r (id K))
    (productMap-first-comp g r)

  evaluate-restrict-inverse-triangle : {R T : CAT Γ} (g : MAP T F) (r : MAP R T)
    → evaluate-restrict e g r =₂ (evaluation-restriction-triangle g r) ⁻¹
  evaluate-restrict-inverse-triangle g r =
    (inverse-composite (e ◁ productMap-first-comp g r)
      (comp-assoc (productMap r (id K)) (productMap g (id K)) e)) ⁻¹ ∙
      comp₌-cong (id₌ ((comp-assoc (productMap r (id K)) (productMap g (id K)) e) ⁻¹))
        (postWhisker-inverse e (productMap-first-comp g r))

  evaluation-substitution-frame : {Q R T : CAT Γ} (g : MAP T F) (r : MAP R T) (s : MAP Q R)
    → (evaluation-restriction-triangle g (r ∘ s) ∙
        ((evaluate e g ◁ productMap-first-comp r s) ∙
          comp-assoc (productMap s (id K)) (productMap r (id K)) (evaluate e g))) =₂
      (evaluate-cong e (comp-assoc s r g) ∙
        (evaluation-restriction-triangle (g ∘ r) s ∙
          (evaluation-restriction-triangle g r ▷ productMap s (id K))))
  evaluation-substitution-frame g r s = post-compatible
    (restriction-diagram (productMap r (id K)) (productMap s (id K)) (productMap (r ∘ s) (id K))
      (productMap-first-comp r s)) e
    (evaluation (productMap-first-comp g (r ∘ s)) (productMap-first-comp g r)
      (productMap-first-comp (g ∘ r) s) (productMap-cong (comp-assoc s r g) (id₌ (id K))))
    (productMap-first-comp-assoc K g r s)

  evaluate-restrict-assoc : {Q R T : CAT Γ} (g : MAP T F) (r : MAP R T) (s : MAP Q R)
    → (evaluate-restrict e g (r ∘ s) ∙ evaluate-cong e (comp-assoc s r g)) =₂
      ((evaluate e g ◁ productMap-first-comp r s) ∙
        (comp-assoc (productMap s (id K)) (productMap r (id K)) (evaluate e g) ∙
          ((evaluate-restrict e g r ▷ productMap s (id K)) ∙ evaluate-restrict e (g ∘ r) s)))
  evaluate-restrict-assoc g r s =
    (comp₌-assoc (evaluate e g ◁ productMap-first-comp r s)
      (comp-assoc S R (evaluate e g)) ((evaluate-restrict e g r ▷ S) ∙ evaluate-restrict e (g ∘ r) s)) ∙
      (comp₌-cong (id₌ delta) normalize-inverse ∙
        (inv-comp-left W (delta ∙ p ⁻¹) ∙
          (comp₌-cong (id₌ (W ⁻¹))
            ((square-to-changeEndpoints p W delta Z (evaluation-substitution-frame g r s)) ⁻¹) ∙
            comp₌-cong (evaluate-restrict-inverse-triangle g (r ∘ s)) (id₌ Z))))
    where
    S = productMap s (id K)
    R = productMap r (id K)
    U = evaluation-restriction-triangle g r
    V = evaluation-restriction-triangle (g ∘ r) s
    W = evaluation-restriction-triangle g (r ∘ s)
    Z = evaluate-cong e (comp-assoc s r g)
    delta = (evaluate e g ◁ productMap-first-comp r s) ∙ comp-assoc S R (evaluate e g)
    p = V ∙ (U ▷ S)
    normalize-inverse : p ⁻¹ =₂ ((evaluate-restrict e g r ▷ S) ∙ evaluate-restrict e (g ∘ r) s)
    normalize-inverse = comp₌-cong
      ((preWhisker S ◁ (evaluate-restrict-inverse-triangle g r) ⁻¹) ∙ (preWhisker-inverse U S) ⁻¹)
      ((evaluate-restrict-inverse-triangle (g ∘ r) s) ⁻¹) ∙ inverse-composite V (U ▷ S)
```
