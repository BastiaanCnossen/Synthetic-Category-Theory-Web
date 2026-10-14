# Evaluating a comparison with a mapped cone

A comparison between a diagram-valued cone and the image of a given cone
evaluates to a comparison with that same cone. This retains the matching
and both leg identifications, including when the diagram-valued cone was
obtained by a pullback factorization.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.MappedConeComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (conePre-assoc; coneIso-pre)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones 𝒯 M ℱ P
  using (mappedCone)
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationCones as Evaluation
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.MappedEvaluationCones as Mapped

module At {T C D E X Γ : CAT} {f : MAP C E} {g : MAP D E}
  (v : Obj-abs T) (s : Cone f g X) (F : MAP Γ (Fun T X))
  (q : Cone (funPost {C = T} f) (funPost g) Γ)
  (Φ : ConeIso (conePre F (mappedCone T s)) q) where
  module Eval = Evaluation.EvaluationCone 𝒯 M ℱ P v f g
    using (normalized-cone; module Induced; module Act)
  module Known = Mapped.MappedAt 𝒯 M ℱ P v s using (comparison)
  evaluated = Eval.Induced.mapCone q

  comparison : ConeIso (conePre (evaluate v ∘ F) s) evaluated
  comparison = coneIso-compose (Eval.Act.map-iso Φ)
    (coneIso-compose (coneIso-inverse (Eval.Act.map-pre F (mappedCone T s)))
      (coneIso-compose
        (coneIso-pre F (coneIso-inverse
          (coneIso-compose Known.comparison (Eval.normalized-cone (mappedCone T s)))))
        (coneIso-inverse (conePre-assoc F (evaluate v) s))))
```
