# Corner matchings and the chosen vertex frames

The bottom and top corner matchings compare the two ways of reaching the
same outer vertex. This comparison survives restriction along any triangle
family, with the original associators. It connects the three corner laws
to the endpoint triangle of the long edge.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using (zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using (d₀; d₁; d₂; vertex₀; vertex₂; d₁-zero; d₂-zero; d₀-one; d₁-one; face-bottom; face-top)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (ev₀; ev₁; evAt; evAt-pre; evAt-cong)
open import SCT.VolumeI.Chapter02.Section01.Triangles
  using (Triangles; edge₀; edge₁; edge₂; evaluation-point-cong; evaluation-point-comp)

module CornerRestriction {Γ : Context} {P T A B C : CAT Γ}
  (l : MAP A C) (r : MAP B C) (cone : Cone l r T)
  {v : MAP T C} (a : (l ∘ Cone.left cone) =₁ v) (b : (r ∘ Cone.right cone) =₁ v)
  (given : (b ∙ Cone.match cone) =₂ a) (sigma : MAP P T) where
  left-frame = restrict-triangle l (Cone.left cone) a sigma
  right-frame = restrict-triangle r (Cone.right cone) b sigma
  matching = Cone.match (cone-restrict sigma cone)
  private
    assocL = comp-assoc sigma (Cone.left cone) l
    assocR = comp-assoc sigma (Cone.right cone) r
    aa = a ▷ sigma
    bb = b ▷ sigma
    middle = Cone.match cone ▷ sigma
  compatibility : (right-frame ∙ matching) =₂ left-frame
  compatibility = comp₌-cong
      ((preWhisker sigma ◁ given) ∙ (preWhisker-comp₌ b (Cone.match cone) sigma) ⁻¹)
      (id₌ (assocL ⁻¹)) ∙
    (((comp₌-assoc bb middle (assocL ⁻¹)) ⁻¹) ∙
      (comp₌-cong (id₌ bb) (inv-comp-left assocR (middle ∙ (assocL ⁻¹))) ∙
        comp₌-assoc bb (assocR ⁻¹) matching))

private
  module _ {Γ : Context} where
    bottom-point : (d₂-zero {Γ = Γ} ∙ face-bottom) =₂ d₁-zero
    bottom-point = comp-inv-left d₂-zero d₁-zero
    top-point : (d₀-one {Γ = Γ} ∙ (face-top ⁻¹)) =₂ d₁-one
    top-point = cancel-right face-top
      ((comp-inv-left d₁-one d₀-one) ⁻¹ ∙ inv-comp-right d₀-one face-top)

    junction : {X C : CAT Γ} {a b c d z : MAP X C}
      (p : a =₁ b) (q : c =₁ d) (delta : b =₁ d)
      (u : b =₁ z) (v : d =₁ z) (given : (v ∙ delta) =₂ u)
      → ((v ∙ q) ∙ (q ⁻¹ ∙ (delta ∙ p))) =₂ (u ∙ p)
    junction p q delta u v given = comp₌-cong given (id₌ p) ∙
      (((comp₌-assoc v delta p) ⁻¹) ∙
        (comp₌-cong (id₌ v) (comp-inv-left q (delta ∙ p)) ∙
          comp₌-assoc v q (q ⁻¹ ∙ (delta ∙ p))))

module TriangleCornerFrames {Γ : Context} (C : CAT Γ) where
  source-cone : Cone (ev₀ {C = C}) ev₀ (Triangles C)
  source-cone = record
    { left = edge₁; right = edge₂
    ; match = (evAt-pre zero d₂) ⁻¹ ∙ (evAt-cong face-bottom ∙ evAt-pre zero d₁) }
  target-cone : Cone (ev₁ {C = C}) ev₁ (Triangles C)
  target-cone = record
    { left = edge₁; right = edge₀
    ; match = (evAt-pre one d₀) ⁻¹ ∙ (evAt-cong (face-top ⁻¹) ∙ evAt-pre one d₁) }
  long-source = evAt-cong {C = C} d₁-zero ∙ evAt-pre zero d₁
  first-source = evAt-cong {C = C} d₂-zero ∙ evAt-pre zero d₂
  long-target = evAt-cong {C = C} d₁-one ∙ evAt-pre one d₁
  second-target = evAt-cong {C = C} d₀-one ∙ evAt-pre one d₀
  source-junction : (first-source ∙ Cone.match source-cone) =₂ long-source
  source-junction = junction (evAt-pre zero d₁) (evAt-pre zero d₂) (evAt-cong face-bottom)
    (evAt-cong d₁-zero) (evAt-cong d₂-zero)
    (evaluation-point-cong bottom-point ∙ (evaluation-point-comp d₂-zero face-bottom) ⁻¹)
  target-junction : (second-target ∙ Cone.match target-cone) =₂ long-target
  target-junction = junction (evAt-pre one d₁) (evAt-pre one d₀) (evAt-cong (face-top ⁻¹))
    (evAt-cong d₁-one) (evAt-cong d₀-one)
    (evaluation-point-cong top-point ∙ (evaluation-point-comp d₀-one (face-top ⁻¹)) ⁻¹)
  module Source {P : CAT Γ} (sigma : MAP P (Triangles C)) =
    CornerRestriction ev₀ ev₀ source-cone long-source first-source source-junction sigma
  module Target {P : CAT Γ} (sigma : MAP P (Triangles C)) =
    CornerRestriction ev₁ ev₁ target-cone long-target second-target target-junction sigma
```
