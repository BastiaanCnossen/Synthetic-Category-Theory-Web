# Normalized evaluation of precomposition components

The chosen curried unit and counit evaluate to the paired original
components. The comparison keeps the identity-product normalization and
both endpoint changes.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionNormalizedComponents
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S using (uncurry-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cancel; retarget-cong)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.FunctorCategoryEvaluation as Evaluation
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionTriangleFrames as Frames

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module A = Adjunction adj
  module Evaluated = Evaluation.At 𝒯 M ℱ P I E S adj K
  module B = Evaluated.Precomposition
  module LeftFrames = Frames.At 𝒯 M ℱ K l r B.unit-target
  module RightFrames = Frames.At 𝒯 M ℱ K r l B.counit-source
  X = Fun C K
  Y = Fun D K
  e : MAP (X × C) K
  e = funEval
  d : MAP (Y × D) K
  d = funEval
  unit-diagram : MorphismExpression (e ∘ pair pr₁ pr₂) (e ∘ pair pr₁ (r ∘ (l ∘ pr₂)))
  unit-diagram = post-expression e (pair-expression (identity-expression pr₁) (A.unit-at pr₂))
  counit-diagram : MorphismExpression (d ∘ pair pr₁ (l ∘ (r ∘ pr₂))) (d ∘ pair pr₁ pr₂)
  counit-diagram = post-expression d (pair-expression (identity-expression pr₁) (A.counit-at pr₂))
  unit-source : funUncurry (id X) =₁ (e ∘ pair pr₁ pr₂)
  unit-source = (B.evaluation-identity C) ⁻¹
  counit-target : funUncurry (id Y) =₁ (d ∘ pair pr₁ pr₂)
  counit-target = (B.evaluation-identity D) ⁻¹

  abstract
    unit-comparison : ExpressionIso (retarget-expression (uncurry-expression B.unit) unit-source B.unit-target) unit-diagram
    unit-comparison = expressionIso-compose (retarget-cancel unit-diagram (B.evaluation-identity C) (B.unit-target ⁻¹))
      (expressionIso-compose (retarget-expressionIso B.unit-comparison unit-source (B.unit-target ⁻¹ ⁻¹))
        (retarget-cong (uncurry-expression B.unit) (idIso unit-source) ((inverse-inverse B.unit-target) ⁻¹)))

    counit-comparison : ExpressionIso (retarget-expression (uncurry-expression B.counit) B.counit-source counit-target) counit-diagram
    counit-comparison = expressionIso-compose (retarget-cancel counit-diagram (B.counit-source ⁻¹) (B.evaluation-identity D))
      (expressionIso-compose (retarget-expressionIso B.counit-comparison (B.counit-source ⁻¹ ⁻¹) counit-target)
        (retarget-cong (uncurry-expression B.counit) ((inverse-inverse B.counit-source) ⁻¹) (idIso counit-target)))
```
