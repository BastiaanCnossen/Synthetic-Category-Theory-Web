# Uncurrying the postcomposition action

The action of `funPost F` on transformations evaluates to postcomposition
by `F`. The endpoint changes are precisely `funPost-uncurry`, with its
chosen restriction and associator comparisons.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingFunctorPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting 𝒯 M ℱ P I E using (post-composite)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingPostcomposition as Uncurrying
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphicPostcomposition as Identified

module At {Γ X C D : CAT} (F : MAP C D) {f g : MAP Γ (Fun X C)} (α : MorphismExpression f g) where
  module U = Uncurrying.At 𝒯 M ℱ P I E S (funPost F) α
  module Beta = Identified.At 𝒯 M ℱ P I E (funPost-β F) U.paired
  original = uncurry-expression (post-expression (funPost F) α)
  source-restriction = funUncurry-restrict (funPost F) f
  target-restriction = funUncurry-restrict (funPost F) g
  source-beta = funPost-β F ▷ productMap f (id X)
  target-beta = funPost-β F ▷ productMap g (id X)
  source-assoc = comp-assoc (productMap f (id X)) funEval F
  target-assoc = comp-assoc (productMap g (id X)) funEval F

  abstract
    intermediate : ExpressionIso (retarget-expression original
        (source-beta ∙ source-restriction) (target-beta ∙ target-restriction))
      (post-expression (F ∘ funEval) U.paired)
    intermediate = expressionIso-compose Beta.value
      (expressionIso-compose (retarget-expressionIso U.comparison source-beta target-beta)
        (expressionIso-inverse (retarget-assoc original source-restriction target-restriction source-beta target-beta)))

    value : ExpressionIso (retarget-expression original (funPost-uncurry F f) (funPost-uncurry F g))
      (post-expression F (uncurry-expression α))
    value = expressionIso-compose (post-composite funEval F U.paired)
      (expressionIso-compose (retarget-expressionIso intermediate source-assoc target-assoc)
        (expressionIso-inverse (retarget-assoc original
          (source-beta ∙ source-restriction) (target-beta ∙ target-restriction) source-assoc target-assoc)))
```
