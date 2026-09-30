# Reflecting triangle identities after evaluation

A triangle between transformations of functors can be checked after
uncurrying and changing its two endpoints. The same middle frame is used
for both legs, so composition cancels that change coherently.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingTriangleReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingReflection 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cancel)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as Identity

module At {Γ X C : CAT} {f g : MAP Γ (Fun X C)}
  (α : MorphismExpression f g) (β : MorphismExpression g f)
  {h k : MAP (Γ × X) C} (p : funUncurry f =₁ h) (q : funUncurry g =₁ k) where
  first = retarget-expression (uncurry-expression α) p q
  second = retarget-expression (uncurry-expression β) q p

  abstract
    reflect : ExpressionIso (compose-expression first second) (identity-expression h) →
      ExpressionIso (compose-expression α β) (identity-expression f)
    reflect ξ = uncurry-reflect
      (expressionIso-compose (expressionIso-inverse (uncurry-identity f))
        (expressionIso-compose (Identity.At.comparison 𝒯 M ℱ P I E (p ⁻¹))
          (expressionIso-compose
            (retarget-expressionIso (expressionIso-compose ξ
                (expressionIso-inverse (retarget-composition (uncurry-expression α) (uncurry-expression β) p q p)))
              (p ⁻¹) (p ⁻¹))
            (expressionIso-compose (expressionIso-inverse (retarget-cancel
                (compose-expression (uncurry-expression α) (uncurry-expression β)) p p))
              (expressionIso-inverse (uncurry-composition α β))))))
```
