# Identity expressions in products

The pair of two identity expressions is the identity of the paired
functor. The two projection comparisons retain their endpoint frames.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductIdentities
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionReflection 𝒯 M ℱ I
  using (product-expression-reflect)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E
  using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (retarget-reflect)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions as Pairing
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as Identity

module At {Γ C D : CAT} (x : MAP Γ C) (y : MAP Γ D) where
  module Paired = Pairing.At 𝒯 M ℱ I (identity-expression x) (identity-expression y)
    using (first-projection; second-projection)

  module Projection {T : CAT} (π : MAP (C × D) T) (z : MAP Γ T)
    (β : (π ∘ pair x y) =₁ z)
    (projection : ExpressionIso
      (retarget-expression (post-expression π (pair-expression (identity-expression x) (identity-expression y))) β β)
      (identity-expression z)) where
    abstract
      identity-comparison : ExpressionIso
        (retarget-expression (post-expression π (identity-expression (pair x y))) β β)
        (identity-expression z)
      identity-comparison = expressionIso-compose (Identity.At.comparison 𝒯 M ℱ P I E β)
        (retarget-expressionIso (post-identity π (pair x y)) β β)

      comparison : ExpressionIso
        (post-expression π (pair-expression (identity-expression x) (identity-expression y)))
        (post-expression π (identity-expression (pair x y)))
      comparison = retarget-reflect β β
        (expressionIso-compose (expressionIso-inverse identity-comparison) projection)

  abstract
    comparison : ExpressionIso (pair-expression (identity-expression x) (identity-expression y))
      (identity-expression (pair x y))
    comparison = product-expression-reflect
      (Projection.comparison pr₁ x (pair-β₁ x y) Paired.first-projection)
      (Projection.comparison pr₂ y (pair-β₂ x y) Paired.second-projection)
```
