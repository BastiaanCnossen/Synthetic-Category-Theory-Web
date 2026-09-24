# Naturality of constant diagrams

Postcomposing a constant diagram makes the constant diagram on its image.
Uncurrying identifies both routes with postcomposition of the first
projection. This compares the actual identity-arrow functors used in the
definition of a groupoid.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section04.ConstantFunctoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public

constant-natural : (T : CAT) {C D : CAT} (f : MAP C D) →
  (funPost f ∘ constantDiagram T C) =₁ (constantDiagram T D ∘ f)
constant-natural T {C} {D} f = funReflect _ _ (right ⁻¹ ∙ left)
  where
  left : (funUncurry (funPost f ∘ constantDiagram T C)) =₁ (f ∘ pr₁)
  left = (f ◁ funCurry-β pr₁) ∙ funPost-uncurry f (constantDiagram T C)
  right : (funUncurry (constantDiagram T D ∘ f)) =₁ (f ∘ pr₁)
  right = pair-β₁ (f ∘ pr₁) (id T ∘ pr₂) ∙
    ((funCurry-β pr₁ ▷ productMap f (id T)) ∙
      funUncurry-restrict (constantDiagram T D) f)
```
