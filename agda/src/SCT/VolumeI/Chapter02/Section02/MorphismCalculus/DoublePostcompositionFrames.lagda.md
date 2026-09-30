# Frames under two postcompositions

Retargeting an expression commutes with two successive postcompositions.
For a composite functor the source and target include its associators.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DoublePostcompositionFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget; retarget-assoc)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting 𝒯 M ℱ P I E
  using (post-composite)

abstract
  double-post-retarget : {Γ B C D : CAT} (F : MAP B C) (G : MAP C D)
    {x y x′ y′ : MAP Γ B} (f : MorphismExpression x y) (p : x =₁ x′) (q : y =₁ y′) →
    ExpressionIso (post-expression G (post-expression F (retarget-expression f p q)))
      (retarget-expression (post-expression G (post-expression F f)) (G ◁ (F ◁ p)) (G ◁ (F ◁ q)))
  double-post-retarget F G f p q = expressionIso-compose
    (post-retarget G (post-expression F f) (F ◁ p) (F ◁ q))
    (post-expressionIso G (post-retarget F f p q))

  post-composite-frames : {Γ B C D : CAT} (F : MAP B C) (G : MAP C D)
    {x y x′ y′ : MAP Γ B} (f : MorphismExpression x y) (p : x =₁ x′) (q : y =₁ y′) →
    ExpressionIso (retarget-expression (post-expression (G ∘ F) f)
      ((G ◁ (F ◁ p)) ∙ comp-assoc x F G) ((G ◁ (F ◁ q)) ∙ comp-assoc y F G))
      (post-expression G (post-expression F (retarget-expression f p q)))
  post-composite-frames F G {x} {y} f p q = expressionIso-compose
    (expressionIso-inverse (double-post-retarget F G f p q))
    (expressionIso-compose
      (retarget-expressionIso (post-composite F G f) (G ◁ (F ◁ p)) (G ◁ (F ◁ q)))
      (expressionIso-inverse (retarget-assoc (post-expression (G ∘ F) f)
        (comp-assoc x F G) (comp-assoc y F G) (G ◁ (F ◁ p)) (G ◁ (F ◁ q)))))

  double-post-id : {Γ B C D : CAT} (F : MAP B C) (G : MAP C D) (x : MAP Γ B) →
    (G ◁ (F ◁ idIso x)) =₂ idIso (G ∘ (F ∘ x))
  double-post-id F G x = postWhisker-idIso G (F ∘ x) ∙ (postWhisker G ◁ postWhisker-idIso F x)

  double-post-composition : {Γ B C D : CAT} (F : MAP B C) (G : MAP C D)
    {x y z : MAP Γ B} (p : y =₁ z) (q : x =₁ y) →
    (G ◁ (F ◁ (p ∙ q))) =₂ ((G ◁ (F ◁ p)) ∙ (G ◁ (F ◁ q)))
  double-post-composition F G p q = postWhisker-isoComp-at G (F ◁ p) (F ◁ q) ∙
    (postWhisker G ◁ postWhisker-isoComp-at F p q)
```
