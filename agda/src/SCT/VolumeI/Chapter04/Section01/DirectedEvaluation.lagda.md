# Directed evaluation

The two maps in `cons:Directed_Evaluation_Map` send an arrow to its
image together with its chosen source or target. Both endpoint frames
come from the existing evaluation and postcomposition calculus.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.DirectedEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedPullbacks 𝒯 M ℱ P I public

module Evaluation {A B : CAT} (f : MAP A B) where
  module Left = DirectedPullback f (id B)
  module Right = DirectedPullback (id B) f

  left-expression : MorphismExpression (f ∘ ev₀) (id B ∘ (f ∘ ev₁))
  left-expression = record
    { arrow = funPost f
    ; source-frame = evaluate-post zero f
    ; target-frame = (comp-unitˡ (f ∘ ev₁)) ⁻¹ ∙ evaluate-post one f }

  right-expression : MorphismExpression (id B ∘ (f ∘ ev₀)) (f ∘ ev₁)
  right-expression = record
    { arrow = funPost f
    ; source-frame = (comp-unitˡ (f ∘ ev₀)) ⁻¹ ∙ evaluate-post zero f
    ; target-frame = evaluate-post one f }

  directed-ev₀ : MAP (Ar A) Left.category
  directed-ev₀ = Left.intro ev₀ (f ∘ ev₁) left-expression

  directed-ev₁ : MAP (Ar A) Right.category
  directed-ev₁ = Right.intro (f ∘ ev₀) ev₁ right-expression

  directed-ev₀-β = Left.intro-β ev₀ (f ∘ ev₁) left-expression
  directed-ev₁-β = Right.intro-β (f ∘ ev₀) ev₁ right-expression

  directed-ev₀-image : (Left.diagram ∘ directed-ev₀) =₁ (funPost f)
  directed-ev₀-image = ConeIso.leftIso directed-ev₀-β

  directed-ev₁-image : (Right.diagram ∘ directed-ev₁) =₁ (funPost f)
  directed-ev₁-image = ConeIso.leftIso directed-ev₁-β

  directed-ev₀-base : (Left.base ∘ directed-ev₀) =₁ (pair ev₀ (f ∘ ev₁))
  directed-ev₀-base = ConeIso.rightIso directed-ev₀-β

  directed-ev₁-base : (Right.base ∘ directed-ev₁) =₁ (pair (f ∘ ev₀) ev₁)
  directed-ev₁-base = ConeIso.rightIso directed-ev₁-β
```
