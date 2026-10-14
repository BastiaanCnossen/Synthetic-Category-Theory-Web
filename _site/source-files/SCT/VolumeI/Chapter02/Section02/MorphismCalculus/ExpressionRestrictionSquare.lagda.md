# Restriction along a commutative square

Two iterated restrictions compare using the specified identification of
the composite parameter maps. Their endpoint frames contain exactly the
two associators and that identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionSquare
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cancel)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expression-compose; restrict-expression-parameter)

module At {Γ Δ Ω Θ C : CAT} {x y : MAP Γ C} (α : MorphismExpression x y)
  (r : MAP Ω Γ) (s : MAP Δ Ω) (u : MAP Θ Γ) (v : MAP Δ Θ) (κ : (r ∘ s) =₁ (u ∘ v)) where
  old = restrict-expression (restrict-expression α r) s
  new = restrict-expression (restrict-expression α u) v
  source-left = (x ◁ κ) ∙ comp-assoc s r x
  target-left = (y ◁ κ) ∙ comp-assoc s r y
  source-right = comp-assoc v u x
  target-right = comp-assoc v u y
  source-change = source-right ⁻¹ ∙ source-left
  target-change = target-right ⁻¹ ∙ target-left

  abstract
    to-common : ExpressionIso (retarget-expression old source-left target-left)
      (restrict-expression α (u ∘ v))
    to-common = expressionIso-compose (restrict-expression-parameter α κ)
      (expressionIso-compose (retarget-expressionIso (restrict-expression-compose α r s) (x ◁ κ) (y ◁ κ))
        (expressionIso-inverse (retarget-assoc old (comp-assoc s r x) (comp-assoc s r y) (x ◁ κ) (y ◁ κ))))

    value : ExpressionIso (retarget-expression old source-change target-change) new
    value = expressionIso-compose (retarget-cancel new source-right target-right)
      (expressionIso-compose
        (retarget-expressionIso (expressionIso-inverse (restrict-expression-compose α u v))
          (source-right ⁻¹) (target-right ⁻¹))
        (expressionIso-compose (retarget-expressionIso to-common (source-right ⁻¹) (target-right ⁻¹))
          (expressionIso-inverse (retarget-assoc old source-left target-left (source-right ⁻¹) (target-right ⁻¹)))))
```
