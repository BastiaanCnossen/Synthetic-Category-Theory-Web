# Composition of left and right fibrations

For `prop:Left_Fibrations_Closed_Under_Composition`, paste the two
endpoint evaluation squares. The postcomposition comparison identifies
the pasted square with the evaluation square of the composite, including
its matching. Pasting cancellation gives the converse when the second
functor is a fibration. The same proof works at either endpoint.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section02.Composition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneIso-inverse)
import SCT.VolumeI.Chapter01.Section06.Pasting.VerticalPasting as Pasting
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.EvaluationComposition as EvaluationComposition
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module At (v : Obj-abs [1]) where
  square : {A B : CAT} (f : MAP A B) → Cone (evaluate {C = B} v) f (Ar A)
  square f = record { left = funPost f ; right = evaluate v ; match = evaluate-post v f }

  module Composite {A B C : CAT} (f : MAP A B) (g : MAP B C)
    (eg : IsPullback (square g)) where
    module Paste = Pasting.Vertical 𝒯 P f g (evaluate v) (square g) (square f) eg
    module Compare = EvaluationComposition.Composite 𝒯 M ℱ {T = [1]} f g
    module Endpoint = Compare.At v

    abstract
      match-normal : (evaluate-post v (g ∘ f) ∙ (evaluate v ◁ Compare.comparison)) =₂
        Cone.match Paste.square
      match-normal = isoComp-cong (idIso (Endpoint.assocBase ⁻¹)) Endpoint.endpoint ∙
        (cancel-left Endpoint.assocBase Endpoint.result) ⁻¹

    comparison : ConeIso Paste.square (square (g ∘ f))
    comparison = record
      { leftIso = Compare.comparison ; rightIso = idIso (evaluate v)
      ; compatible = isoComp-cong ((postWhisker-idIso (g ∘ f) (evaluate v)) ⁻¹)
          (idIso (Cone.match Paste.square)) ∙
          (isoComp-unitˡ-at (Cone.match Paste.square)) ⁻¹ ∙ match-normal }

    abstract
      square-isPullback : IsPullback (square f) → IsPullback (square (g ∘ f))
      square-isPullback ef = pullback-cone-invariant comparison (Paste.square-isPullback ef)

      cancel-isPullback : IsPullback (square (g ∘ f)) → IsPullback (square f)
      cancel-isPullback e = Paste.cancel-isPullback
        (pullback-cone-invariant (coneIso-inverse comparison) e)

left-composition : {A B C : CAT} (f : MAP A B) (g : MAP B C) →
  IsEquiv (Evaluation.directed-ev₀ f) → IsEquiv (Evaluation.directed-ev₀ g) →
  IsEquiv (Evaluation.directed-ev₀ (g ∘ f))
left-composition f g ef eg = Criterion.pullback-to-left (g ∘ f)
  (At.Composite.square-isPullback zero f g (Criterion.left-to-pullback g eg) (Criterion.left-to-pullback f ef))

right-composition : {A B C : CAT} (f : MAP A B) (g : MAP B C) →
  IsEquiv (Evaluation.directed-ev₁ f) → IsEquiv (Evaluation.directed-ev₁ g) →
  IsEquiv (Evaluation.directed-ev₁ (g ∘ f))
right-composition f g ef eg = Criterion.pullback-to-right (g ∘ f)
  (At.Composite.square-isPullback one f g (Criterion.right-to-pullback g eg) (Criterion.right-to-pullback f ef))

left-cancellation : {A B C : CAT} (f : MAP A B) (g : MAP B C) →
  IsEquiv (Evaluation.directed-ev₀ g) → IsEquiv (Evaluation.directed-ev₀ (g ∘ f)) →
  IsEquiv (Evaluation.directed-ev₀ f)
left-cancellation f g eg e = Criterion.pullback-to-left f
  (At.Composite.cancel-isPullback zero f g (Criterion.left-to-pullback g eg)
    (Criterion.left-to-pullback (g ∘ f) e))

right-cancellation : {A B C : CAT} (f : MAP A B) (g : MAP B C) →
  IsEquiv (Evaluation.directed-ev₁ g) → IsEquiv (Evaluation.directed-ev₁ (g ∘ f)) →
  IsEquiv (Evaluation.directed-ev₁ f)
right-cancellation f g eg e = Criterion.pullback-to-right f
  (At.Composite.cancel-isPullback one f g (Criterion.right-to-pullback g eg)
    (Criterion.right-to-pullback (g ∘ f) e))
```
