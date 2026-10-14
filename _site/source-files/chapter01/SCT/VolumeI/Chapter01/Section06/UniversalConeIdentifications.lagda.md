# Prescribed identifications in a universal cone

The supplied complete cone comparison determines an identification of vertex
maps with both prescribed projection images. These are the consequences
needed by nested insertion; no equality of higher action witnesses is asserted.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.UniversalConeIdentifications where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle; restrict-change-square)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (factor-through-postWhisker)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares

module _ {Γ : Context} where
  module UniversalConeIdentification {C D E T S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (t : Cone f g T) (e : IsPullback t) (h k : MAP S T)
    (Φ : ConeIdentification₁ (cone-restrict h t) (cone-restrict k t)) where
    comparison = pullback-factor t

    factor-cone-law : (r : MAP S T) → ConeIdentification₁
      (cone-restrict (comparison ∘ r) (pullback-cone f g)) (cone-restrict r t)
    factor-cone-law r = cone-compose (cone-identification-restrict-One r (pullback-factor-β t))
      (cone-inverse (cone-restrict-assoc r comparison (pullback-cone f g)))

    transported : ConeIdentification₁
      (cone-restrict (comparison ∘ h) (pullback-cone f g))
      (cone-restrict (comparison ∘ k) (pullback-cone f g))
    transported = cone-compose (cone-inverse (factor-cone-law k))
      (cone-compose Φ (factor-cone-law h))

    module Chosen = PullbackRecovery (comparison ∘ h) (comparison ∘ k)
      (cone-identification transported)

    chosen : Fact.Factorization (postWhisker comparison) Chosen.identification
    chosen = factor-through-postWhisker comparison e Chosen.identification

    identification : h =₁ k
    identification = Fact.factor chosen

    postWhisker-law : (comparison ◁ identification) =₂ Chosen.identification
    postWhisker-law = Fact.triangle chosen

    projection-law : {B : CAT Γ} (π : MAP (Pullback f g) B) (q : MAP T B)
      (b : (π ∘ comparison) =₁ q) (α : (q ∘ h) =₁ (q ∘ k))
      → (π ◁ Chosen.identification) =₂
          ((restrict-triangle π comparison b k) ⁻¹ ∙
            (α ∙ restrict-triangle π comparison b h))
      → (q ◁ identification) =₂ α
    projection-law π q b α prescribed = cancel-right (restrict-triangle π comparison b h)
      (comp-inv-left (restrict-triangle π comparison b k) (α ∙ restrict-triangle π comparison b h) ∙
        (comp₌-cong (id₌ (restrict-triangle π comparison b k)) prescribed ∙
          (comp₌-cong (id₌ (restrict-triangle π comparison b k))
            (postWhisker π ◁ postWhisker-law) ∙
            (unconst-sides₌ (restrict-change-square π comparison q b identification)) ⁻¹)))

    restriction₁ : (Cone.left t ◁ identification) =₂ ConeIdentification₁.left Φ
    restriction₁ = projection-law pullback₁ (Cone.left t)
      (pullback-factor-β₁ t) (ConeIdentification₁.left Φ) Chosen.left-image

    restriction₂ : (Cone.right t ◁ identification) =₂ ConeIdentification₁.right Φ
    restriction₂ = projection-law pullback₂ (Cone.right t)
      (pullback-factor-β₂ t) (ConeIdentification₁.right Φ) Chosen.right-image
```
