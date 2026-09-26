# Uniqueness of functor categories

For `prop:Uniqueness_Of_Functor_Categories`, curry either evaluation into
the other representing category. Uncurrying the two composites gives the
inverse comparisons. The comparison with evaluation remains explicit.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section07.Uniqueness
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.Representation 𝒯 M

module Uniqueness {F G C D : CAT} (e : MAP (F × C) D) (e′ : MAP (G × C) D)
  (universal : IsFunctorCategory e) (universal′ : IsFunctorCategory e′) where
  module Left = Representing e universal
  module Right = Representing e′ universal′

  forward : MAP G F
  forward = Left.curry e′
  backward : MAP F G
  backward = Right.curry e

  evaluation-comparison : (Left.uncurry forward) =₁ e′
  evaluation-comparison = Left.curry-β e′

  forward-backward : (forward ∘ backward) =₁ (id F)
  forward-backward = Left.reflect _ _ (Left.uncurry-id ⁻¹ ∙
    (Right.curry-β e ∙ ((evaluation-comparison ▷ productMap backward (id C)) ∙ Left.uncurry-restrict forward backward)))

  backward-forward : (backward ∘ forward) =₁ (id G)
  backward-forward = Right.reflect _ _ (Right.uncurry-id ⁻¹ ∙
    (evaluation-comparison ∙ ((Right.curry-β e ▷ productMap forward (id C)) ∙ Right.uncurry-restrict backward forward)))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward ; sectionIso = backward-forward ⁻¹ ; retractionIso = forward-backward ⁻¹ }
```
