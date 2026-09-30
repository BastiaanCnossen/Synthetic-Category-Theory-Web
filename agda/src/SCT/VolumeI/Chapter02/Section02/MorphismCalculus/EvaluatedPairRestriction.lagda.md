# Restriction of evaluated pairs

Restriction and specified endpoint changes of both coordinates commute
with pairing and evaluation. The comparison retains the product and
composition identifications at both ends.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedPairRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I using (restrict-post-frames)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionRestriction as Restriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as Frames

module At {Γ Δ A B C : CAT} {x y : MAP Γ A} {u v : MAP Γ B}
  (α : MorphismExpression x y) (β : MorphismExpression u v)
  (h : MAP Δ Γ) (F : MAP (A × B) C)
  {x′ y′ : MAP Δ A} {u′ v′ : MAP Δ B}
  (p : (x ∘ h) =₁ x′) (q : (y ∘ h) =₁ y′)
  (r : (u ∘ h) =₁ u′) (s : (v ∘ h) =₁ v′)
  {α′ : MorphismExpression x′ y′} {β′ : MorphismExpression u′ v′}
  (ξ : ExpressionIso (retarget-expression (restrict-expression α h) p q) α′)
  (ζ : ExpressionIso (retarget-expression (restrict-expression β h) r s) β′) where
  source-product : (pair x u ∘ h) =₁ pair x′ u′
  source-product = pair-cong p r ∙ pair-pre x u h
  target-product : (pair y v ∘ h) =₁ pair y′ v′
  target-product = pair-cong q s ∙ pair-pre y v h
  source-frame = (F ◁ source-product) ∙ comp-assoc h (pair x u) F
  target-frame = (F ◁ target-product) ∙ comp-assoc h (pair y v) F

  abstract
    paired : ExpressionIso (retarget-expression (restrict-expression (pair-expression α β) h)
      source-product target-product) (pair-expression α′ β′)
    paired = expressionIso-compose (pair-expression-cong ξ ζ)
      (expressionIso-compose (Frames.At.value 𝒯 M ℱ I (restrict-expression α h) (restrict-expression β h) p q r s)
        (expressionIso-compose (retarget-expressionIso (Restriction.At.value 𝒯 M ℱ P I E S α β h)
            (pair-cong p r) (pair-cong q s))
          (expressionIso-inverse (retarget-assoc (restrict-expression (pair-expression α β) h)
            (pair-pre x u h) (pair-pre y v h) (pair-cong p r) (pair-cong q s)))))

    value : ExpressionIso (retarget-expression (restrict-expression (post-expression F (pair-expression α β)) h)
      source-frame target-frame) (post-expression F (pair-expression α′ β′))
    value = expressionIso-compose (post-expressionIso F paired)
      (restrict-post-frames F (pair-expression α β) h source-product target-product)
```
