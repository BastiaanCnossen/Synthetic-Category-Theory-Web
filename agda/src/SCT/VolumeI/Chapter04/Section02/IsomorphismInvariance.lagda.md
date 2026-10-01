# Isomorphic functors have the same fibration property

A specified isomorphism of functors transports either evaluation square.
The postcomposition comparison retains its evaluation equation, so the
transport applies to the specified pullback square, including its matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.EvaluationIsomorphisms as EvaluationIso

module SCT.VolumeI.Chapter04.Section02.IsomorphismInvariance
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯
  using (changeLeft; coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P using (module ChangeLeft)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)

module At (v : Obj-abs [1]) {A B : CAT} {f g : MAP A B} (α : f =₁ g) where
  module Post = EvaluationIso.Along 𝒯 M ℱ {T = [1]} α using (comparison; module At)
  module Endpoint = Post.At v using (endpoint)
  square : (h : MAP A B) → Cone (evaluate {C = B} v) h (Ar A)
  square h = record { left = funPost h ; right = evaluate v ; match = evaluate-post v h }

  changed : Cone (evaluate {C = B} v) g (Ar A)
  changed = record { left = funPost f ; right = evaluate v
    ; match = (α ▷ evaluate v) ∙ evaluate-post v f }

  comparison : ConeIso changed (square g)
  comparison = record { leftIso = Post.comparison ; rightIso = idIso (evaluate v)
    ; compatible = isoComp-cong ((postWhisker-idIso g (evaluate v)) ⁻¹) (idIso (Cone.match changed)) ∙
        ((isoComp-unitˡ-at (Cone.match changed)) ⁻¹ ∙ Endpoint.endpoint) }

  abstract
    square-isPullback : IsPullback (square f) → IsPullback (square g)
    square-isPullback ef = pullback-cone-invariant comparison
      (pullback-cone-invariant
        (cone-match-change _ _ _ _
          (isoComp-cong (inverse-inverse (α ▷ evaluate v)) (inverse-inverse (evaluate-post v f)) ∙
            inverse-composite ((evaluate-post v f) ⁻¹) ((α ▷ evaluate v) ⁻¹)))
        (pullback-swap (changeLeft α (coneSwap (square f)))
          (ChangeLeft.preserve α (evaluate v) (coneSwap (square f))
            (pullback-swap (square f) ef))))

left-invariance : {A B : CAT} {f g : MAP A B} → f =₁ g →
  IsEquiv (Evaluation.directed-ev₀ f) → IsEquiv (Evaluation.directed-ev₀ g)
left-invariance {f = f} {g} α ef = Criterion.pullback-to-left g
  (At.square-isPullback zero α (Criterion.left-to-pullback f ef))

right-invariance : {A B : CAT} {f g : MAP A B} → f =₁ g →
  IsEquiv (Evaluation.directed-ev₁ f) → IsEquiv (Evaluation.directed-ev₁ g)
right-invariance {f = f} {g} α ef = Criterion.pullback-to-right g
  (At.square-isPullback one α (Criterion.right-to-pullback f ef))
```
