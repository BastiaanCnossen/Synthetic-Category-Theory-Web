# Endpoint frames from a recovered projection comparison

A prescribed comparison of one edge determines its vertex frame. This
calculation retains the projection image of the recovered pullback
identification and both chosen beta triangles. Postcomposition transports
the whole square, rather than choosing another vertex comparison.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.RecoveredVertexFrame where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; post-triangle; unrestrict-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-change)

module RecoveredVertexFrame {Γ : Context} {P T K A C : CAT Γ}
  (r : MAP A C) (pi : MAP K A) (q : MAP T K) (sigma : MAP P T) (pair : MAP P K)
  (delta : (q ∘ sigma) =₁ pair)
  {edge : MAP T A} {arrow : MAP P A}
  (before : (pi ∘ q) =₁ edge) (after : (pi ∘ pair) =₁ arrow)
  (comparison : (edge ∘ sigma) =₁ arrow)
  (image : (pi ◁ delta) =₂ (after ⁻¹ ∙ (comparison ∙ restrict-triangle pi q before sigma)))
  {v : MAP T C} {x : MAP P C}
  (b : (r ∘ edge) =₁ v) (c : (r ∘ arrow) =₁ x) where
  private
    restricted = restrict-triangle r edge b sigma
    action = r ◁ comparison
    vertex-assoc = comp-assoc sigma edge r
    outer-assoc = comp-assoc sigma q (r ∘ pi)
    old-post = post-triangle r pi q before
    new-post = post-triangle r pi pair after
    square : (after ∙ (pi ◁ delta)) =₂
      (comparison ∙ restrict-triangle pi q before sigma)
    square = comp-inv-left after (comparison ∙ restrict-triangle pi q before sigma) ∙
      comp₌-cong (id₌ after) image
    change = post-triangle-change r pi q sigma pair delta before after comparison square

  frame : (v ∘ sigma) =₁ x
  frame = (c ∙ action) ∙ restricted ⁻¹
  old-frame : ((r ∘ pi) ∘ q) =₁ v
  old-frame = b ∙ old-post
  new-frame : ((r ∘ pi) ∘ pair) =₁ x
  new-frame = c ∙ new-post

  private
    vertex-square : (c ∙ (action ∙ vertex-assoc)) =₂ (frame ∙ (b ▷ sigma))
    vertex-square = unrestrict-square r edge sigma arrow comparison b c frame
      ((inv-comp-right (c ∙ action) restricted) ⁻¹)

  compatibility : (new-frame ∙ (((r ∘ pi) ◁ delta) ∙ outer-assoc)) =₂
    (frame ∙ (old-frame ▷ sigma))
  compatibility = comp₌-cong (id₌ frame) ((preWhisker-comp₌ b old-post sigma) ⁻¹) ∙
    (comp₌-assoc frame (b ▷ sigma) (old-post ▷ sigma) ∙
      (comp₌-cong vertex-square (id₌ (old-post ▷ sigma)) ∙
        (((comp₌-assoc c (action ∙ vertex-assoc) (old-post ▷ sigma)) ⁻¹) ∙
          (comp₌-cong (id₌ c) ((comp₌-assoc action vertex-assoc (old-post ▷ sigma)) ⁻¹) ∙
            (comp₌-cong (id₌ c) change ∙
              comp₌-assoc c new-post (((r ∘ pi) ◁ delta) ∙ outer-assoc))))))
```
