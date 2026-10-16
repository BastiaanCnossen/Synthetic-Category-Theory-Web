# The action of point evaluation on identifications

Point evaluation preserves identifications between identifications, their
composition, identities and inverses. All four laws concern the native
point action with its original constant first coordinate. Triangle vertices
and generic diagram corners share these calculations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PointEvaluationAction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; postWhisker-id₌; preWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-cong; pair⁼-id)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (inverse-unique; comp₌-inverseˡ-One)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (evAt; evAt-cong; insert)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-fixed-first-comp)

module _ {Γ : Context} {I C : CAT Γ} where
  private
    F : CAT Γ
    F = Fun I C
    e : MAP (F × I) C
    e = funEval
    t : MAP F One
    t = terminate F
    native-id : id F =₁ id F
    native-id = const {P = One} (id₌ (id F))

  evaluation-point-cong : {a b : MAP One I} {α β : a =₁ b}
    → α =₂ β → evAt-cong {C = C} α =₂ evAt-cong β
  evaluation-point-cong given = postWhisker e ◁
    pair⁼-cong (id₌ (const (id₌ (id F)))) (preWhisker t ◁ given)

  evaluation-point-comp : {a b d : MAP One I} (β : b =₁ d) (α : a =₁ b)
    → evAt-cong {C = C} (β ∙ α) =₂ (evAt-cong β ∙ evAt-cong α)
  evaluation-point-comp β α =
    postWhisker-comp₌ e (pair⁼ (const (id₌ (id F))) (β ▷ t))
      (pair⁼ (const (id₌ (id F))) (α ▷ t)) ∙
    (postWhisker e ◁
      (pair⁼-fixed-first-comp (id F) (β ▷ t) (α ▷ t) ∙
        pair⁼-cong (id₌ (const (id₌ (id F)))) (preWhisker-comp₌ β α t)))

  evaluation-point-id : (a : MAP One I)
    → evAt-cong {C = C} (id₌ a) =₂ id₌ (evAt a)
  evaluation-point-id a = postWhisker-id₌ e (insert a) ∙
    (postWhisker e ◁ (const-One (id₌ (insert a)) ∙
      (pair⁼-id (id F) (const a) ∙
        pair⁼-cong (id₌ native-id)
          (((const-One (id₌ (const a))) ⁻¹) ∙ preWhisker-id₌ a t))))

  evaluation-point-inverse : {a b : MAP One I} (alpha : a =₁ b)
    → evAt-cong {C = C} (alpha ⁻¹) =₂ (evAt-cong alpha) ⁻¹
  evaluation-point-inverse {a} alpha =
    (inverse-unique (evAt-cong {C = C} alpha) (evAt-cong (alpha ⁻¹))
      (((const-One (id₌ (evAt {C = C} a))) ⁻¹) ∙
        (evaluation-point-id a ∙
          (evaluation-point-cong (comp₌-inverseˡ-One alpha) ∙
            ((evaluation-point-comp (alpha ⁻¹) alpha) ⁻¹))))) ⁻¹
```
