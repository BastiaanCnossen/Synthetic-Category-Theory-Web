# Framed evaluation of precomposition

Precomposition restricts an evaluated transformation in its object
coordinate. This comparison retains specified endpoint changes.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingPrecompositionFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; restrict-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expressionIso)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingFunctorPrecomposition as Pre

module At {Γ K C : CAT} {f g : MAP Γ (Fun K C)} (α : MorphismExpression f g)
  {h k : MAP (Γ × K) C} (p : funUncurry f =₁ h) (q : funUncurry g =₁ k)
  {β : MorphismExpression h k} (ξ : ExpressionIso (retarget-expression (uncurry-expression α) p q) β) where

  abstract
    value : {B : CAT} (r : MAP B K) →
      let σ = productMap (id Γ) r in
      ExpressionIso (retarget-expression (uncurry-expression (post-expression (funPre {D = C} r) α))
        ((p ▷ σ) ∙ funPre-uncurry r f) ((q ▷ σ) ∙ funPre-uncurry r g))
        (restrict-expression β σ)
    value {B} r = expressionIso-compose (restrict-expressionIso ξ σ)
      (expressionIso-compose (expressionIso-inverse (restrict-retarget (uncurry-expression α) p q σ))
        (expressionIso-compose (retarget-expressionIso (Pre.At.value 𝒯 M ℱ P I E S r α) (p ▷ σ) (q ▷ σ))
          (expressionIso-inverse (retarget-assoc (uncurry-expression (post-expression (funPre {D = C} r) α))
            (funPre-uncurry r f) (funPre-uncurry r g) (p ▷ σ) (q ▷ σ)))))
      where
      σ : MAP (Γ × B) (Γ × K)
      σ = productMap (id Γ) r
```
