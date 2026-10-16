# The native corner of a square diagram

The horizontal and vertical sides meet at the chosen product point. Their
vertex comparisons use the existing product restriction, unit and constant
comparisons. Evaluation carries this independently specified corner to a
comparison of the two side endpoints. Its equation with the two vertex
frames is proved before considering any currying permutation.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCorners where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (const-evaluate; comp₌-cong; comp₌-assoc; comp-inv-left)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; cone-restrict)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt; evAt-pre; evAt-cong)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationAction
  using (evaluation-point-comp; evaluation-point-inverse)
open import SCT.VolumeI.Chapter02.Section02.SquareCoordinates using (coinsert)

module SquareCorner {Γ : Context} (a b : MAP One ([1] {Γ = Γ})) where
  private
    I = [1] {Γ = Γ}
  vertex : MAP One (I × I)
  vertex = pair a b
  horizontal-vertex : (coinsert a ∘ b) =₁ vertex
  horizontal-vertex = pair⁼ (const-evaluate a b) (comp-unitˡ b) ∙
    pair-pre (const a) (id I) b
  vertical-vertex : (insert b ∘ a) =₁ vertex
  vertical-vertex = pair⁼ (comp-unitˡ a) (const-evaluate b a) ∙
    pair-pre (id I) (const b) a
  corner : (coinsert a ∘ b) =₁ (insert b ∘ a)
  corner = vertical-vertex ⁻¹ ∙ horizontal-vertex

  module Evaluated (C : CAT Γ) where
    private
      p = evAt-pre {C = C} b (coinsert a)
      q = evAt-pre {C = C} a (insert b)
      hp = evAt-cong {C = C} horizontal-vertex
      vp = evAt-cong {C = C} vertical-vertex
      middle = evAt-cong {C = C} corner
    horizontal : (evAt b ∘ funPre {D = C} (coinsert a)) =₁ evAt vertex
    horizontal = hp ∙ p
    vertical : (evAt a ∘ funPre {D = C} (insert b)) =₁ evAt vertex
    vertical = vp ∙ q
    matching : (evAt b ∘ funPre {D = C} (coinsert a)) =₁
      (evAt a ∘ funPre {D = C} (insert b))
    matching = q ⁻¹ ∙ (middle ∙ p)
    private
      middle-image : middle =₂ (vp ⁻¹ ∙ hp)
      middle-image = comp₌-cong (evaluation-point-inverse {C = C} vertical-vertex) (id₌ hp) ∙
        evaluation-point-comp {C = C} (vertical-vertex ⁻¹) horizontal-vertex
    vertex-equation : (vertical ∙ matching) =₂ horizontal
    vertex-equation = comp₌-cong (comp-inv-left vp hp) (id₌ p) ∙
      (comp₌-cong (comp₌-cong (id₌ vp) middle-image) (id₌ p) ∙
        ((comp₌-assoc vp middle p) ⁻¹ ∙
          (comp₌-cong (id₌ vp) (comp-inv-left q (middle ∙ p)) ∙
            comp₌-assoc vp q (q ⁻¹ ∙ (middle ∙ p)))))
    cone : Cone (evAt {C = C} b) (evAt a) (Fun (I × I) C)
    cone = record { left = funPre (coinsert a); right = funPre (insert b); match = matching }
    at-family : {P : CAT Γ} → MAP P (Fun (I × I) C) → Cone (evAt b) (evAt a) P
    at-family sigma = cone-restrict sigma cone
```
