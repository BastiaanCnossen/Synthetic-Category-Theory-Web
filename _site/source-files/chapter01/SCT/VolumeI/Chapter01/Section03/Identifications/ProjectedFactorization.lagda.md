# Transporting a factorization through specified base frames

A comparison of factorizations can be projected along a map of bases.
If the projected base maps have specified identifications with simpler
ones, the resulting factor triangle still satisfies the comparison
square. Its frame is the actual projected triangle, conjugated by those
specified identifications. This records the calculation needed to forget
the middle vertex without replacing the chosen triangle.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.ProjectedFactorization where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (preWhisker-comp-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle; post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-change)

module ProjectedFactorization {Γ : Context} {X Y T S B : CAT Γ}
  (baseY : MAP Y S) (baseX : MAP X S) (baseT : MAP T S)
  (q : MAP X Y) (sigma : MAP T X) (p : MAP T Y)
  (q-frame : (baseY ∘ q) =₁ baseX) (p-frame : (baseY ∘ p) =₁ baseT)
  (delta : (q ∘ sigma) =₁ p) (frame : (baseX ∘ sigma) =₁ baseT)
  (given : (p-frame ∙ (baseY ◁ delta)) =₂
    (frame ∙ restrict-triangle baseY q q-frame sigma))
  (k : MAP S B) (outerY : MAP Y B) (outerX : MAP X B) (outerT : MAP T B)
  (atY : (k ∘ baseY) =₁ outerY) (atX : (k ∘ baseX) =₁ outerX)
  (atT : (k ∘ baseT) =₁ outerT)
  (q-outer : (outerY ∘ q) =₁ outerX) (p-outer : (outerY ∘ p) =₁ outerT)
  (q-image : (atX ∙ post-triangle k baseY q q-frame) =₂ (q-outer ∙ (atY ▷ q)))
  (p-image : (atT ∙ post-triangle k baseY p p-frame) =₂ (p-outer ∙ (atY ▷ p))) where
  private
    D = post-triangle k baseY q q-frame
    E = post-triangle k baseY p p-frame
    V = (k ◁ frame) ∙ comp-assoc sigma baseX k
    before = atT ∙ V
    restrictedX = atX ▷ sigma
    W = (atY ▷ q) ▷ sigma
    outerA = comp-assoc sigma q outerY
    originalA = comp-assoc sigma q (k ∘ baseY)
    outer-delta = outerY ◁ delta
    original-delta = (k ∘ baseY) ◁ delta
    transported = post-triangle-change k baseY q sigma p delta q-frame p-frame frame given
    crossing = unconst-sides₌ (interchange-fixedOuter atY delta)

  projected-frame : (outerX ∘ sigma) =₁ outerT
  projected-frame = before ∙ restrictedX ⁻¹

  private
    left₁ = comp₌-assoc projected-frame (q-outer ▷ sigma) W
    left₂ = comp₌-cong (id₌ projected-frame)
      ((preWhisker-comp₌ q-outer (atY ▷ q) sigma) ⁻¹)
    left₃ = comp₌-cong (id₌ projected-frame) (preWhisker sigma ◁ (q-image ⁻¹))
    left₄ = comp₌-cong (id₌ projected-frame) (preWhisker-comp₌ atX D sigma)
    left₅ = (comp₌-assoc projected-frame restrictedX (D ▷ sigma)) ⁻¹
    left₆ = comp₌-cong (inv-comp-right before restrictedX) (id₌ (D ▷ sigma))
    left-normal : ((projected-frame ∙ (q-outer ▷ sigma)) ∙ W) =₂
      (before ∙ (D ▷ sigma))
    left-normal = left₆ ∙ (left₅ ∙ (left₄ ∙ (left₃ ∙ (left₂ ∙ left₁))))

    right₁ = comp₌-assoc p-outer outer-delta (outerA ∙ W)
    right₂ = comp₌-cong (id₌ p-outer)
      (comp₌-cong (id₌ outer-delta) (preWhisker-comp-One atY q sigma))
    right₃ = comp₌-cong (id₌ p-outer)
      ((comp₌-assoc outer-delta (atY ▷ (q ∘ sigma)) originalA) ⁻¹)
    right₄ = comp₌-cong (id₌ p-outer)
      (comp₌-cong (crossing ⁻¹) (id₌ originalA))
    right₅ = comp₌-cong (id₌ p-outer)
      (comp₌-assoc (atY ▷ p) original-delta originalA)
    right₆ = (comp₌-assoc p-outer (atY ▷ p) (original-delta ∙ originalA)) ⁻¹
    right₇ = comp₌-cong (p-image ⁻¹) (id₌ (original-delta ∙ originalA))
    right₈ = comp₌-assoc atT E (original-delta ∙ originalA)
    right₉ = comp₌-cong (id₌ atT) transported
    right₉a = comp₌-cong (id₌ atT)
      ((comp₌-assoc (k ◁ frame) (comp-assoc sigma baseX k) (D ▷ sigma)) ⁻¹)
    right₁₀ = (comp₌-assoc atT V (D ▷ sigma)) ⁻¹
    right-normal : ((p-outer ∙ outer-delta) ∙ (outerA ∙ W)) =₂
      (before ∙ (D ▷ sigma))
    right-normal = right₁₀ ∙ (right₉a ∙ (right₉ ∙ (right₈ ∙ (right₇ ∙ (right₆ ∙
      (right₅ ∙ (right₄ ∙ (right₃ ∙ (right₂ ∙ right₁)))))))))
    corner : ((p-outer ∙ outer-delta) ∙ outerA) =₂
      (projected-frame ∙ (q-outer ▷ sigma))
    corner = cancel-right W ((left-normal ⁻¹) ∙
      (right-normal ∙ comp₌-assoc (p-outer ∙ outer-delta) outerA W))

  compatible : (p-outer ∙ (outerY ◁ delta)) =₂
    (projected-frame ∙ restrict-triangle outerY q q-outer sigma)
  compatible = comp₌-assoc projected-frame (q-outer ▷ sigma) (outerA ⁻¹) ∙
    (comp₌-cong corner (id₌ (outerA ⁻¹)) ∙
      ((comp-inv-right (p-outer ∙ outer-delta) outerA) ⁻¹))
```
