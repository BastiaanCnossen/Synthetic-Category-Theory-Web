# Triangle identities with a fixed coordinate

Pairing with an identity transformation and applying a functor preserves
an identity composite. Both legs use the same product endpoint frames.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.FixedCoordinateTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (product-composition; pair-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductIdentities as Identities

module At {Γ A B C : CAT} (x : MAP Γ A) {y z : MAP Γ B}
  (α : MorphismExpression y z) (β : MorphismExpression z y) (F : MAP (A × B) C) where
  first = post-expression F (pair-expression (identity-expression x) α)
  second = post-expression F (pair-expression (identity-expression x) β)

  abstract
    value : ExpressionIso (compose-expression α β) (identity-expression y) →
      ExpressionIso (compose-expression first second) (identity-expression (F ∘ pair x y))
    value ξ = expressionIso-compose (post-identity F (pair x y))
      (expressionIso-compose (post-expressionIso F (Identities.At.comparison 𝒯 M ℱ P I E S x y))
        (expressionIso-compose (post-expressionIso F (pair-expression-cong (left-unit (identity-expression x)) ξ))
          (expressionIso-compose (post-expressionIso F (product-composition
              (identity-expression x) (identity-expression x) α β))
            (post-composition F (pair-expression (identity-expression x) α) (pair-expression (identity-expression x) β)))))
```
