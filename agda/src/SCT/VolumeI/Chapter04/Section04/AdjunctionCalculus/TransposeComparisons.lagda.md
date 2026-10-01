# Transposition preserves comparisons and endpoint changes

An endpoint-preserving comparison can be transposed in either direction.
If the endpoints themselves are identified, the unit and counit component
comparisons give the corresponding identification after transposition.
The images of the specified endpoint identifications are retained.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction as Restriction

module Comparisons {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) where
  private
    module A = Adjunction adj
    module R = Restriction.Components 𝒯 M ℱ P I E S adj using (unit-parameter; counit-parameter)

  abstract
    transpose-cong : {Γ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      {α β : MorphismExpression (l ∘ x) y} → ExpressionIso α β →
      ExpressionIso (A.transpose x y α) (A.transpose x y β)
    transpose-cong x y Φ = compose-expression-cong (expressionIso-id (A.unit-at x)) (post-expressionIso r Φ)

    untranspose-cong : {Γ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      {α β : MorphismExpression x (r ∘ y)} → ExpressionIso α β →
      ExpressionIso (A.untranspose x y α) (A.untranspose x y β)
    untranspose-cong x y Φ = compose-expression-cong (post-expressionIso l Φ) (expressionIso-id (A.counit-at y))

    transpose-retarget : {Γ : CAT} {x x′ : MAP Γ C} {y y′ : MAP Γ D}
      (α : MorphismExpression (l ∘ x) y) (ξ : x =₁ x′) (ζ : y =₁ y′) →
      ExpressionIso (retarget-expression (A.transpose x y α) ξ (r ◁ ζ))
        (A.transpose x′ y′ (retarget-expression α (l ◁ ξ) ζ))
    transpose-retarget {x = x} α ξ ζ = expressionIso-compose
      (compose-expression-cong (R.unit-parameter ξ) (expressionIso-inverse (post-retarget r α (l ◁ ξ) ζ)))
      (expressionIso-inverse (retarget-composition (A.unit-at x) (post-expression r α)
        ξ (r ◁ (l ◁ ξ)) (r ◁ ζ)))

    untranspose-retarget : {Γ : CAT} {x x′ : MAP Γ C} {y y′ : MAP Γ D}
      (β : MorphismExpression x (r ∘ y)) (ξ : x =₁ x′) (ζ : y =₁ y′) →
      ExpressionIso (retarget-expression (A.untranspose x y β) (l ◁ ξ) ζ)
        (A.untranspose x′ y′ (retarget-expression β ξ (r ◁ ζ)))
    untranspose-retarget {y = y} β ξ ζ = expressionIso-compose
      (compose-expression-cong (expressionIso-inverse (post-retarget l β ξ (r ◁ ζ))) (R.counit-parameter ζ))
      (expressionIso-inverse (retarget-composition (post-expression l β) (A.counit-at y)
        (l ◁ ξ) (l ◁ (r ◁ ζ)) ζ))
```
