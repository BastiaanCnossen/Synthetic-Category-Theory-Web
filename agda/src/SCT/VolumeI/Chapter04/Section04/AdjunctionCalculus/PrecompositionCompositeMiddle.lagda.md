# The composite route to the precomposition middle

Both chosen middle frames agree with evaluation through the composite
precomposition functor. The statements use the actual curried components
and their selected frames.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionCompositeMiddle
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P using (preComp)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PrecompositionNormalizedComponents as Normalized
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionMiddleEvaluation as Middle
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionMiddleRestriction as Restriction

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module N = Normalized.At 𝒯 M ℱ P I E S adj K
  module B = N.B
  module Left = Middle.At 𝒯 M ℱ P K l r
  module Right = Middle.At 𝒯 M ℱ P K r l

  module LeftRestriction = Restriction.At 𝒯 M ℱ P K l r
  module RightRestriction = Restriction.At 𝒯 M ℱ P K r l

  abstract
    left-middle : N.LeftFrames.middle =₂
      (Left.Image.nE ∙ (funPre-uncurry (l ∘ r) B.left ∙ funUncurryIso (preComp r l ▷ B.left)))
    left-middle = Left.value

    right-middle : N.RightFrames.middle =₂
      (Right.Image.nE ∙ (funPre-uncurry (r ∘ l) B.right ∙ funUncurryIso (preComp l r ▷ B.right)))
    right-middle = Right.value

    left-restricted-middle : N.LeftFrames.middle =₂
      (LeftRestriction.SeparationResult.Ξ ∙
        ((B.counit-source ▷ LeftRestriction.σ) ∙ funUncurry-restrict (B.left ∘ B.right) B.left))
    left-restricted-middle = LeftRestriction.value

    right-restricted-middle : N.RightFrames.middle =₂
      (RightRestriction.SeparationResult.Ξ ∙
        ((B.unit-target ▷ RightRestriction.σ) ∙ funUncurry-restrict (B.right ∘ B.left) B.right))
    right-restricted-middle = RightRestriction.value
```
