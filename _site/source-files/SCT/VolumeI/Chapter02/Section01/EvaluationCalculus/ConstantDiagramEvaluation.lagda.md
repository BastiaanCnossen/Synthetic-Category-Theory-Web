# Evaluation of a varying constant diagram

Both the value of the constant diagram and its evaluation parameter may
vary over the same category. The comparison follows directly from the
currying and product projection identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantDiagramEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)

evaluate-constant-at : {Γ I C : CAT} (x : MAP Γ C) (t : MAP Γ I) →
  (funEval ∘ pair (constantDiagram I C ∘ x) t) =₁ x
evaluate-constant-at {I = I} {C} x t = pair-β₁ x t ∙
  ((funCurry-β (pr₁ {C} {I}) ▷ pair x t) ∙
    ((comp-assoc (pair x t) (productMap (constantDiagram I C) (id I)) funEval) ⁻¹ ∙
      (funEval ◁ (pair-cong (idIso (constantDiagram I C ∘ x)) (comp-unitˡ t) ∙
        productMap-pair (constantDiagram I C) (id I) x t) ⁻¹)))
```
