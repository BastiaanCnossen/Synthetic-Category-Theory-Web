# Uncurrying natural transformations

Evaluation of the paired transformation and the fixed domain coordinate
uncurries a natural transformation. The coordinate is written with its
identity functor so that the endpoints are the literal chosen uncurrying
functors. Uncurrying preserves identities and composition with both
endpoint compatibility equations.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I
  using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S
  using (product-composition; pair-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (restrict-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S
  using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E
  using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as Restriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductIdentities as Identities

uncurry-expression : {Γ X C : CAT} {f g : MAP Γ (Fun X C)} →
  MorphismExpression f g → MorphismExpression (funUncurry f) (funUncurry g)
uncurry-expression {X = X} α = post-expression funEval
  (pair-expression (restrict-expression α pr₁) (identity-expression (id X ∘ pr₂)))

abstract
  uncurry-cong : {Γ X C : CAT} {f g : MAP Γ (Fun X C)}
    {α β : MorphismExpression f g} → ExpressionIso α β →
    ExpressionIso (uncurry-expression α) (uncurry-expression β)
  uncurry-cong {X = X} ξ = post-expressionIso funEval
    (pair-expression-cong (restrict-expressionIso ξ pr₁) (expressionIso-id (identity-expression (id X ∘ pr₂))))

  uncurry-identity : {Γ X C : CAT} (f : MAP Γ (Fun X C)) →
    ExpressionIso (uncurry-expression (identity-expression f)) (identity-expression (funUncurry f))
  uncurry-identity {X = X} f = expressionIso-compose (post-identity funEval (productMap f (id X)))
    (expressionIso-compose
      (post-expressionIso funEval (Identities.At.comparison 𝒯 M ℱ P I E S (f ∘ pr₁) (id X ∘ pr₂)))
      (post-expressionIso funEval
        (pair-expression-cong (Restriction.Restrict.comparison 𝒯 M ℱ P I E f pr₁)
          (expressionIso-id (identity-expression (id X ∘ pr₂))))))

  uncurry-composition : {Γ X C : CAT} {f g h : MAP Γ (Fun X C)}
    (α : MorphismExpression f g) (β : MorphismExpression g h) →
    ExpressionIso (compose-expression (uncurry-expression α) (uncurry-expression β))
      (uncurry-expression (compose-expression α β))
  uncurry-composition {X = X} α β = expressionIso-compose
    (post-expressionIso funEval
      (pair-expression-cong (restrict-composition α β pr₁) (left-unit (identity-expression (id X ∘ pr₂)))))
    (expressionIso-compose
      (post-expressionIso funEval
        (product-composition (restrict-expression α pr₁) (restrict-expression β pr₁)
          (identity-expression (id X ∘ pr₂)) (identity-expression (id X ∘ pr₂))))
      (post-composition funEval
        (pair-expression (restrict-expression α pr₁) (identity-expression (id X ∘ pr₂)))
        (pair-expression (restrict-expression β pr₁) (identity-expression (id X ∘ pr₂)))))
```
