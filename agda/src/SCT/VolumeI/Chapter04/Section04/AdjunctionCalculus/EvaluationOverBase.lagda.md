# The evaluation deformations are identities over the base

After postcomposition by their absorbing evaluation functors, maximum
and minimum become identity expressions. Both endpoint frames are
included in the comparison. The equations on the constant-arrow
section, and hence the adjunctions, remain separate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationOverBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows 𝒯 M ℱ I using (constant-frame)
import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantIdentityComparison as ConstantIdentity
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.EvaluatedSquareExpressions as SquaresOfExpressions
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformations as Deformations
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformationCorners as Corners
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationRestrictionFactorization as Factors

module At (C : CAT) where
  module D = Deformations.At 𝒯 M ℱ P I E C
    using (target-unit; source-counit; module MaximumSource; module MaximumTarget; module MinimumSource; module MinimumTarget)

  constant-expression : (p : MAP (Ar C) C) → MorphismExpression p p
  constant-expression p = record
    { arrow = identityArrow ∘ p
    ; source-frame = constant-frame ev₀ identity-source p
    ; target-frame = constant-frame ev₁ identity-target p }

  module Maximum where
    p : MAP (Ar C) C
    p = ev₁
    source-frame = comp-unitʳ p
    target-frame = constant-frame p identity-target p
    module Source = Corners.Evaluated.MaximumSourceFrame 𝒯 M ℱ P I E S Q R C
      using (horizontal-direct; vertical-direct; corner-matching; comparison)
    module Target = Corners.Evaluated.MaximumTargetFrame 𝒯 M ℱ P I E S Q R C
      using (horizontal-direct; vertical-direct; corner-matching; comparison)
    module SourceBridge = Factors.At.Vertical.Identity 𝒯 M ℱ P I E C max zero max-right-zero
    module TargetBridge = Factors.At.Vertical.Constant 𝒯 M ℱ P I E C max one one max-right-one
    module Evaluated = SquaresOfExpressions.At.Framed.Evaluated 𝒯 M ℱ P I E (funPre {D = C} max)
      D.MaximumSource.comparison D.MaximumTarget.comparison one
      using (horizontal-expression; comparison)

    abstract
      source-direct : Source.vertical-direct =₂ D.MaximumSource.comparison
      source-direct = SourceBridge.comparison ∙ SourceBridge.N.comparison ⁻¹
      target-direct : Target.vertical-direct =₂ D.MaximumTarget.comparison
      target-direct = TargetBridge.comparison ∙ TargetBridge.N.comparison ⁻¹

      horizontal-identity : ExpressionIso
        (retarget-expression Evaluated.horizontal-expression source-frame target-frame)
        (constant-expression p)
      horizontal-identity = record
        { comparison = Source.horizontal-direct
        ; source-compatible = isoComp-assoc-at source-frame (p ◁ D.MaximumSource.comparison) Source.corner-matching ∙
            (isoComp-cong (isoComp-cong (idIso source-frame) (postWhisker p ◁ source-direct))
              (idIso Source.corner-matching) ∙ Source.comparison)
        ; target-compatible = isoComp-assoc-at target-frame (p ◁ D.MaximumTarget.comparison) Target.corner-matching ∙
            (isoComp-cong (isoComp-cong (idIso target-frame) (postWhisker p ◁ target-direct))
              (idIso Target.corner-matching) ∙ Target.comparison) }

      over-base : ExpressionIso
        (retarget-expression (post-expression p D.target-unit) source-frame target-frame)
        (identity-expression p)
      over-base = expressionIso-compose (ConstantIdentity.At.comparison 𝒯 M ℱ P I E p)
        (expressionIso-compose horizontal-identity
          (retarget-expressionIso Evaluated.comparison source-frame target-frame))

  module Minimum where
    p : MAP (Ar C) C
    p = ev₀
    source-frame = constant-frame p identity-source p
    target-frame = comp-unitʳ p
    module Source = Corners.Evaluated.MinimumSourceFrame 𝒯 M ℱ P I E S Q R C
      using (horizontal-direct; vertical-direct; corner-matching; comparison)
    module Target = Corners.Evaluated.MinimumTargetFrame 𝒯 M ℱ P I E S Q R C
      using (horizontal-direct; vertical-direct; corner-matching; comparison)
    module SourceBridge = Factors.At.Vertical.Constant 𝒯 M ℱ P I E C min zero zero min-right-zero
    module TargetBridge = Factors.At.Vertical.Identity 𝒯 M ℱ P I E C min one min-right-one
    module Evaluated = SquaresOfExpressions.At.Framed.Evaluated 𝒯 M ℱ P I E (funPre {D = C} min)
      D.MinimumSource.comparison D.MinimumTarget.comparison zero
      using (horizontal-expression; comparison)

    abstract
      source-direct : Source.vertical-direct =₂ D.MinimumSource.comparison
      source-direct = SourceBridge.comparison ∙ SourceBridge.N.comparison ⁻¹
      target-direct : Target.vertical-direct =₂ D.MinimumTarget.comparison
      target-direct = TargetBridge.comparison ∙ TargetBridge.N.comparison ⁻¹

      horizontal-identity : ExpressionIso
        (retarget-expression Evaluated.horizontal-expression source-frame target-frame)
        (constant-expression p)
      horizontal-identity = record
        { comparison = Source.horizontal-direct
        ; source-compatible = isoComp-assoc-at source-frame (p ◁ D.MinimumSource.comparison) Source.corner-matching ∙
            (isoComp-cong (isoComp-cong (idIso source-frame) (postWhisker p ◁ source-direct))
              (idIso Source.corner-matching) ∙ Source.comparison)
        ; target-compatible = isoComp-assoc-at target-frame (p ◁ D.MinimumTarget.comparison) Target.corner-matching ∙
            (isoComp-cong (isoComp-cong (idIso target-frame) (postWhisker p ◁ target-direct))
              (idIso Target.corner-matching) ∙ Target.comparison) }

      over-base : ExpressionIso
        (retarget-expression (post-expression p D.source-counit) source-frame target-frame)
        (identity-expression p)
      over-base = expressionIso-compose (ConstantIdentity.At.comparison 𝒯 M ℱ P I E p)
        (expressionIso-compose horizontal-identity
          (retarget-expressionIso Evaluated.comparison source-frame target-frame))

```
