# Slice projections are right and left fibrations

For `thm:Slice_Fibrations`, the projection from a slice is a right
fibration and the projection from a coslice is a left fibration. The
triangle presentations and Segal pasting prove their evaluation squares
are pullbacks. The endpoint frame then identifies these maps with the
chosen projections of the original slice definitions.

The proof uses the Segal and commutative-square axioms. It does not use
functoriality of universals or categories in a categorical context.

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
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEvaluationPullbacks as EvaluationSquares

module SCT.VolumeI.Chapter04.Section03.SliceFibrations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I
  using (module Criterion; module Evaluation)
open import SCT.VolumeI.Chapter04.Section02.IsomorphismInvariance 𝒯 M ℱ P I
  using (left-invariance; right-invariance)
open import SCT.VolumeI.Chapter04.Section03.RelativeSlices 𝒯 M ℱ P I
  using (module RelativeSlice; module RelativeCoslice)
open import SCT.VolumeI.Chapter04.Section02.BaseChange 𝒯 M ℱ P I
  using (left-base-change; right-base-change)
open Laws.PullbackStructure P using (pullbackCone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (pullbackCone-isPullback)

abstract
  slice-isRightFibration : {C : CAT} (x : Obj-abs C) →
    IsEquiv (Evaluation.directed-ev₁ (slice-projection x))
  slice-isRightFibration {C} x = right-invariance (comp-unitˡ F.base ∙ F.source-frame)
    (Criterion.pullback-to-right (ev₀ ∘ F.arrow) Square.evaluation-isPullback)
    where
    module F = EndpointFiber (id C) (const x) using (base; arrow; source-frame)
    module Square = EvaluationSquares.Slice 𝒯 M ℱ P I E S Q x using (evaluation-isPullback)

  coslice-isLeftFibration : {C : CAT} (x : Obj-abs C) →
    IsEquiv (Evaluation.directed-ev₀ (coslice-projection x))
  coslice-isLeftFibration {C} x = left-invariance (comp-unitˡ F.base ∙ F.target-frame)
    (Criterion.pullback-to-left (ev₁ ∘ F.arrow) Square.evaluation-isPullback)
    where
    module F = EndpointFiber (const x) (id C) using (base; arrow; target-frame)
    module Square = EvaluationSquares.Coslice 𝒯 M ℱ P I E S Q x using (evaluation-isPullback)

  relative-slice-isRightFibration : {C D : CAT} (f : MAP C D) (d : Obj-abs D) →
    IsEquiv (Evaluation.directed-ev₁ (RelativeSlice.projection f d))
  relative-slice-isRightFibration f d = right-base-change
    (pullbackCone (slice-projection d) f) (pullbackCone-isPullback (slice-projection d) f)
    (slice-isRightFibration d)

  relative-coslice-isLeftFibration : {C D : CAT} (f : MAP C D) (d : Obj-abs D) →
    IsEquiv (Evaluation.directed-ev₀ (RelativeCoslice.projection f d))
  relative-coslice-isLeftFibration f d = left-base-change
    (pullbackCone (coslice-projection d) f) (pullbackCone-isPullback (coslice-projection d) f)
    (coslice-isLeftFibration d)
```
