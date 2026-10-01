# Evaluating the mixed insertion square

This is the mixed restriction comparison for an arbitrary functor
`e : Y × B → C`. Its proof evaluates the already checked product square,
including its specified vertex comparisons. Currying plays no role here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluationVerticalPasting as VerticalPasting
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionRestrictionCompatibility as ProductSquare

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionRestrictionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionEvaluation 𝒯 M ℱ using (evaluate-insertion)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation 𝒯 M using (evaluate-square; change-sides)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯 using (append-five)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)

module At {X Y A B C : CAT}
  (e : MAP (Y × B) C) (h : MAP X Y) (r : MAP A B) (x : Obj-abs A) where
  open ProductSquare.At 𝒯 M ℱ h r x
    using (HA; HB; LX; LY; ix; iy; jx; jy; χX; χY; separation; left; right)
  module Pasted = VerticalPasting.At 𝒯 M e h HA HB ix iy LX LY
    (insert-natural h x) separation
    using (comparison; composite-square; together)
  restriction-evaluation = evaluate-square e HA HB LX LY separation

  abstract
    corner-square :
      (insert-natural h (r ∘ x) ∙ (χY ▷ h)) =₂
        ((HB ◁ χX) ∙ Pasted.composite-square)
    corner-square =
      append-five (HB ◁ χX) (comp-assoc ix LX HB) (separation ▷ ix)
        ((comp-assoc ix HA LY) ⁻¹) (LY ◁ insert-natural h x) (comp-assoc h iy LY) ∙
      (isoComp-cong (ProductSquare.At.comparison 𝒯 M ℱ h r x) (idIso (comp-assoc h iy LY)) ∙
      (isoComp-cong (idIso (insert-natural h (r ∘ x)))
          (cancel-inverse-tail (χY ▷ h) (comp-assoc h iy LY)) ∙
        isoComp-assoc-at (insert-natural h (r ∘ x))
          ((χY ▷ h) ∙ (comp-assoc h iy LY) ⁻¹) (comp-assoc h iy LY)) ⁻¹)

    comparison :
      (evaluate-insertion e h (r ∘ x) ∙
        (((e ◁ χY) ▷ h) ∙ (comp-assoc iy LY e ▷ h))) =₂
      (((e ∘ HB) ◁ χX) ∙
        (comp-assoc ix LX (e ∘ HB) ∙
          ((restriction-evaluation ▷ ix) ∙ evaluate-insertion (e ∘ LY) h x)))
    comparison = isoComp-cong (idIso ((e ∘ HB) ◁ χX)) Pasted.comparison ∙
      (isoComp-assoc-at ((e ∘ HB) ◁ χX) Pasted.together (comp-assoc iy LY e ▷ h) ∙
      (isoComp-cong
        (change-sides e h HB χX χY Pasted.composite-square (insert-natural h (r ∘ x)) corner-square)
        (idIso (comp-assoc iy LY e ▷ h)) ∙
        (isoComp-assoc-at (evaluate-insertion e h (r ∘ x))
          ((e ◁ χY) ▷ h) (comp-assoc iy LY e ▷ h)) ⁻¹))
```
