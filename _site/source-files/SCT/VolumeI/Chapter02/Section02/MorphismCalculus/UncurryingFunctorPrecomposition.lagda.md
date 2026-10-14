# Uncurrying the precomposition action

The action of `funPre {D = D} r` on transformations evaluates to restriction
along the product parameter map. Both endpoint changes are the chosen
`funPre-uncurry` comparisons.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingFunctorPrecomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cancel; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting 𝒯 M ℱ P I E using (post-composite)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I using (restrict-post)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductSeparation as Separation
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingIdentifiedPostcomposition as Identified

module At {Γ B C D : CAT} (r : MAP B C) {f g : MAP Γ (Fun C D)} (α : MorphismExpression f g) where
  module Separate = Separation.At 𝒯 M ℱ P I E S α r
  J : MAP (Fun C D × B) (Fun C D × C)
  J = productMap (id (Fun C D)) r
  σ : MAP (Γ × B) (Γ × C)
  σ = productMap (id Γ) r
  evaluation : MAP (Fun C D × C) D
  evaluation = funEval
  paired : MorphismExpression (productMap f (id B)) (productMap g (id B))
  paired = Separation.external-product 𝒯 M ℱ P I E S α (id B)
  pre-evaluation : funUncurry (funPre {D = D} r) =₁ (evaluation ∘ J)
  pre-evaluation = funPre-β {D = D} r
  original : MorphismExpression (funUncurry (funPre {D = D} r ∘ f)) (funUncurry (funPre {D = D} r ∘ g))
  original = uncurry-expression (post-expression (funPre {D = D} r) α)
  final : MorphismExpression (funUncurry f ∘ σ) (funUncurry g ∘ σ)
  final = restrict-expression (uncurry-expression α) σ
  module Endpoint (h : MAP Γ (Fun C D)) where
    restriction : funUncurry (funPre {D = D} r ∘ h) =₁ (funUncurry (funPre {D = D} r) ∘ productMap h (id B))
    restriction = funUncurry-restrict (funPre {D = D} r) h
    beta : (funUncurry (funPre {D = D} r) ∘ productMap h (id B)) =₁ ((evaluation ∘ J) ∘ productMap h (id B))
    beta = pre-evaluation ▷ productMap h (id B)
    before : ((evaluation ∘ J) ∘ productMap h (id B)) =₁ (evaluation ∘ (J ∘ productMap h (id B)))
    before = comp-assoc (productMap h (id B)) J evaluation
    across : (evaluation ∘ (J ∘ productMap h (id B))) =₁ (evaluation ∘ (productMap h (id C) ∘ σ))
    across = evaluation ◁ productMap-separate h r
    after : (funUncurry h ∘ σ) =₁ (evaluation ∘ (productMap h (id C) ∘ σ))
    after = comp-assoc σ (productMap h (id C)) evaluation
    first : funUncurry (funPre {D = D} r ∘ h) =₁ ((evaluation ∘ J) ∘ productMap h (id B))
    first = beta ∙ restriction
    second : funUncurry (funPre {D = D} r ∘ h) =₁ (evaluation ∘ (J ∘ productMap h (id B)))
    second = before ∙ first
    third : funUncurry (funPre {D = D} r ∘ h) =₁ (evaluation ∘ (productMap h (id C) ∘ σ))
    third = across ∙ second
  module Source = Endpoint f
  module Target = Endpoint g

  abstract
    first : ExpressionIso (retarget-expression original Source.first Target.first)
      (post-expression (evaluation ∘ J) paired)
    first = Identified.At.value 𝒯 M ℱ P I E S (funPre {D = D} r) (evaluation ∘ J) pre-evaluation α

    second : ExpressionIso (retarget-expression original Source.second Target.second)
      (post-expression evaluation Separate.left)
    second = expressionIso-compose (post-composite J evaluation paired)
      (expressionIso-compose (retarget-expressionIso first Source.before Target.before)
        (expressionIso-inverse (retarget-assoc original Source.first Target.first Source.before Target.before)))

    third : ExpressionIso (retarget-expression original Source.third Target.third)
      (post-expression evaluation Separate.right)
    third = expressionIso-compose (post-expressionIso evaluation Separate.value)
      (expressionIso-compose (expressionIso-inverse (post-retarget evaluation Separate.left
          (productMap-separate f r) (productMap-separate g r)))
        (expressionIso-compose (retarget-expressionIso second Source.across Target.across)
          (expressionIso-inverse (retarget-assoc original Source.second Target.second Source.across Target.across))))

    value : ExpressionIso (retarget-expression original (funPre-uncurry r f) (funPre-uncurry r g)) final
    value = expressionIso-compose (retarget-cancel final Source.after Target.after)
      (expressionIso-compose (retarget-expressionIso
          (expressionIso-inverse (restrict-post evaluation (Separation.external-product 𝒯 M ℱ P I E S α (id C)) σ))
          (Source.after ⁻¹) (Target.after ⁻¹))
        (expressionIso-compose (retarget-expressionIso third (Source.after ⁻¹) (Target.after ⁻¹))
          (expressionIso-inverse (retarget-assoc original Source.third Target.third (Source.after ⁻¹) (Target.after ⁻¹)))))
```
