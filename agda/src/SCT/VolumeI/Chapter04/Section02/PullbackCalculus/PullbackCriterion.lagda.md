# The evaluation-square criterion for left and right fibrations

For `lem:Characterization_Left_And_Right_Fibrations`, compare the
one-sided square obtained from the defining directed pullback with the
square given directly by endpoint naturality. The comparison below
retains the prescribed leg identifications and their compatibility with
`evaluate-post`. Thus both implications refer to the specified square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointNormalization 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯
  using (changeLeft-pre; changeLeft-iso)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
  using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullback-cone-invariant)

module Criterion {A B : CAT} (f : MAP A B) where
  open Evaluation f
  module Derived = EvaluationSquares f

  source-square : Cone (ev₀ {B}) f (Ar A)
  source-square = record { left = funPost f ; right = ev₀ ; match = evaluate-post zero f }

  target-square : Cone (ev₁ {B}) f (Ar A)
  target-square = record { left = funPost f ; right = ev₁ ; match = evaluate-post one f }

  source-comparison : ConeIso Derived.source-square source-square
  source-comparison = coneIso-compose
    (SourceNormalization.comparison f ev₀ (f ∘ ev₁) left-expression)
    (coneIso-compose
      (changeLeft-iso (pair-β₁ ev₀ ev₁) (Source.Paste.Paste.flatten-iso f directed-ev₀-β))
      (coneIso-compose
        (changeLeft-iso (pair-β₁ ev₀ ev₁)
          (Source.Paste.Paste.flatten-pre f directed-ev₀ (Source.original f)))
        (changeLeft-pre (pair-β₁ ev₀ ev₁) directed-ev₀ (Source.pasted f))))

  target-comparison : ConeIso Derived.target-square target-square
  target-comparison = coneIso-compose
    (TargetNormalization.comparison f (f ∘ ev₀) ev₁ right-expression)
    (coneIso-compose
      (changeLeft-iso (pair-β₂ ev₀ ev₁) (Target.Paste.Paste.flatten-iso f directed-ev₁-β))
      (coneIso-compose
        (changeLeft-iso (pair-β₂ ev₀ ev₁)
          (Target.Paste.Paste.flatten-pre f directed-ev₁ (Target.original f)))
        (changeLeft-pre (pair-β₂ ev₀ ev₁) directed-ev₁ (Target.pasted f))))

  left-to-pullback : IsEquiv directed-ev₀ → IsPullback source-square
  left-to-pullback e = pullback-cone-invariant source-comparison (Derived.left-to-pullback e)

  pullback-to-left : IsPullback source-square → IsEquiv directed-ev₀
  pullback-to-left e = Derived.pullback-to-left
    (pullback-cone-invariant (coneIso-inverse source-comparison) e)

  right-to-pullback : IsEquiv directed-ev₁ → IsPullback target-square
  right-to-pullback e = pullback-cone-invariant target-comparison (Derived.right-to-pullback e)

  pullback-to-right : IsPullback target-square → IsEquiv directed-ev₁
  pullback-to-right e = Derived.pullback-to-right
    (pullback-cone-invariant (coneIso-inverse target-comparison) e)
```

