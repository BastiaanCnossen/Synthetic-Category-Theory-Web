# Evaluating a framed square expression

The horizontal side of a curried square agrees with evaluation of its
vertical expression. Both endpoint frames are retained; their comparison
is the corner theorem for the same square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.EvaluatedSquareExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-boundary-normal)
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurrying as Currying
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCornerEvaluation as Corners

module At {Γ C : CAT} (W : MAP Γ (Fun ([1] × [1]) C)) where
  module Curry = Currying.At 𝒯 M ℱ W using (nested; module Vertical; module Horizontal)

  module Framed {x y : MAP Γ (Ar C)}
    (p : Curry.Vertical.side zero =₁ x) (q : Curry.Vertical.side one =₁ y) where
    square-expression : MorphismExpression x y
    square-expression = record
      { arrow = Curry.nested
      ; source-frame = p ∙ Curry.Vertical.boundary zero
      ; target-frame = q ∙ Curry.Vertical.boundary one }

    module Evaluated (u : Obj-abs [1]) where
      module Corner (v : Obj-abs [1]) = Corners.At 𝒯 M ℱ P I E W u v
        using (matching; comparison)

      horizontal-expression : MorphismExpression (evaluate u ∘ x) (evaluate u ∘ y)
      horizontal-expression = record
        { arrow = Curry.Horizontal.side u
        ; source-frame = (evaluate u ◁ p) ∙ Corner.matching zero
        ; target-frame = (evaluate u ◁ q) ∙ Corner.matching one }

      abstract
        endpoint : (v : Obj-abs [1]) {z : MAP Γ (Ar C)}
          (r : Curry.Vertical.side v =₁ z) →
          (((evaluate u ◁ r) ∙ Corner.matching v) ∙
            (evaluate v ◁ Curry.Horizontal.comparison u)) =₂
          post-boundary v (evaluate u) Curry.nested (r ∙ Curry.Vertical.boundary v)
        endpoint v r = (post-boundary-normal v (evaluate u) Curry.nested
            (r ∙ Curry.Vertical.boundary v)) ⁻¹ ∙
          isoComp-cong ((postWhisker-isoComp-at (evaluate u) r (Curry.Vertical.boundary v)) ⁻¹)
            (idIso (evaluate-post-at v (evaluate u) Curry.nested)) ∙
          (isoComp-assoc-at (evaluate u ◁ r) (evaluate u ◁ Curry.Vertical.boundary v)
            (evaluate-post-at v (evaluate u) Curry.nested)) ⁻¹ ∙
          isoComp-cong (idIso (evaluate u ◁ r)) ((Corner.comparison v) ⁻¹) ∙
          isoComp-assoc-at (evaluate u ◁ r) (Corner.matching v)
            (evaluate v ◁ Curry.Horizontal.comparison u)

      comparison : ExpressionIso (post-expression (evaluate u) square-expression) horizontal-expression
      comparison = record
        { comparison = Curry.Horizontal.comparison u
        ; source-compatible = endpoint zero p
        ; target-compatible = endpoint one q }
```
