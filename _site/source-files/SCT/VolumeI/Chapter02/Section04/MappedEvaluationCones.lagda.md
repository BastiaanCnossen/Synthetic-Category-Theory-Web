# Evaluation of a mapped cone with specified leg comparisons

The full cone comparison below has the literal `evaluate-post` comparisons
as its legs. Keeping these particular witnesses permits cancellation of
the outside rectangles in the base-change proof for left/right fibrations.
The generic evaluation and uncurrying comparison comes from
`EvaluationCones`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.MappedEvaluationCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.ConeUncurrying 𝒯 M ℱ using (uncurryCone)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeRestriction 𝒯 using (conePre-assoc; coneIso-pre)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (cone-match-change)
import SCT.VolumeI.Chapter01.Section07.MappedCones as Mapped
import SCT.VolumeI.Chapter02.Section04.EvaluationCones as Evaluation

module At {T C D E X : CAT} {f : MAP C E} {g : MAP D E}
  (v : Obj-abs T) (s : Cone (funPost {C = T} f) (funPost g) X) where
  module EC = Evaluation.EvaluationCone 𝒯 M ℱ P v f g
  value = EC.CoordinateEvaluation.read s
  comparison = EC.At.evaluated s

module MappedAt {T C D E X : CAT} {f : MAP C E} {g : MAP D E}
  (v : Obj-abs T) (s : Cone f g X) where
  module MC = Mapped.MappedCone 𝒯 M ℱ P T s
  module Evaluated = At v MC.value

  raw-comparison = coneIso-compose
    (coneIso-inverse (coneRetarget-β (conePre funEval s) _ _
      (MC.Curried.left-β ⁻¹) (MC.Curried.right-β ⁻¹)))
    (cone-match-change _ _ _ _ MC.Curried.match-β)

  curried-comparison : ConeIso (uncurryCone MC.value) (conePre funEval s)
  curried-comparison = coneIso-adjust raw-comparison
    MC.Curried.left-β MC.Curried.right-β
    (inverse-inverse MC.Curried.left-β ∙ isoComp-unitʳ-at ((MC.Curried.left-β ⁻¹) ⁻¹))
    (inverse-inverse MC.Curried.right-β ∙ isoComp-unitʳ-at ((MC.Curried.right-β ⁻¹) ⁻¹))

  comparison : ConeIso Evaluated.value (conePre (evaluate v) s)
  comparison = coneIso-compose
    (conePre-assoc (insert v) funEval s)
    (coneIso-compose (coneIso-pre (insert v) curried-comparison) Evaluated.comparison)
```
