# Selected representations under restriction and postcomposition

These two ordinary terms retain a supplied uncurrying representation triangle
under parameter restriction or postcomposition. They use its original beta
and the chosen functoriality/evaluation comparison, without point data.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.DiagramRepresentations where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-uncurry)

module _ {Γ : Context} where
  represented-postcomposition : {I P C D : CAT Γ}
    (F : MAP C D) (h : MAP P (Fun I C)) (H : MAP (P × I) C)
    (beta : funUncurry h =₁ H)
    → funUncurry (funPost {C = I} F ∘ h) =₁ (F ∘ H)
  represented-postcomposition F h H beta = (F ◁ beta) ∙ funPost-uncurry F h

module _ {Γ : Context} where
  represented-restriction : {I C P Q : CAT Γ}
    (h : MAP P (Fun I C)) (H : MAP (P × I) C)
    (beta : funUncurry h =₁ H) (r : MAP Q P)
    → funUncurry (h ∘ r) =₁ (H ∘ productMap r (id I))
  represented-restriction {I = I} {C = C} h H beta r =
    (beta ▷ productMap r (id I)) ∙ evaluate-restrict (funEval {C = I} {D = C}) h r

```
