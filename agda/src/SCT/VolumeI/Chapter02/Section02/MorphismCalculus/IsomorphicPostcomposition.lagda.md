# Postcomposition by identified functors

An identification between functors compares their actions on a
transformation. Its components provide the two endpoint changes.
Naturality on the underlying interval diagram supplies both boundary
equations before the comparison is curried.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphicPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ using (application-natural)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.CurryPostcomposition as Post

module At {Γ C D : CAT} {F G : MAP C D} (η : F =₁ G)
  {x y : MAP Γ C} (α : MorphismExpression x y) where
  module R = Diagrams.Recovery 𝒯 M ℱ P I E α
  module First = Post.At 𝒯 M ℱ P I E F R.H R.p R.q
  module Second = Post.At 𝒯 M ℱ P I E G R.H R.p R.q
  sourceF = (F ◁ R.p) ∙ comp-assoc (insert zero) R.H F
  targetF = (F ◁ R.q) ∙ comp-assoc (insert one) R.H F
  sourceG = (G ◁ R.p) ∙ comp-assoc (insert zero) R.H G
  targetG = (G ◁ R.q) ∙ comp-assoc (insert one) R.H G
  module Compared = Diagrams.At 𝒯 M ℱ P I E (F ∘ R.H) (G ∘ R.H) (η ▷ R.H)
    ((η ▷ x) ∙ sourceF) ((η ▷ y) ∙ targetF) sourceG targetG
    (application-natural R.H (insert zero) R.p η) (application-natural R.H (insert one) R.q η)

  abstract
    value : ExpressionIso (retarget-expression (post-expression F α) (η ▷ x) (η ▷ y))
      (post-expression G α)
    value = expressionIso-compose (post-expressionIso G (expressionIso-inverse R.comparison))
      (expressionIso-compose (expressionIso-inverse Second.comparison)
        (expressionIso-compose Compared.comparison
          (expressionIso-compose (Diagrams.retarget-curried 𝒯 M ℱ P I E (F ∘ R.H)
              sourceF targetF (η ▷ x) (η ▷ y))
            (retarget-expressionIso
              (expressionIso-compose First.comparison (post-expressionIso F R.comparison)) (η ▷ x) (η ▷ y)))))
```
