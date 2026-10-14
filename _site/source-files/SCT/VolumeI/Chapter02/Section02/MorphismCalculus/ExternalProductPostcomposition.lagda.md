# Postcomposition of an external product transformation

Applying a product functor acts on the transformation and on the fixed
functor separately. The endpoint comparison is the existing compositor
for product functors.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; retarget-cancel)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I using (restrict-post)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFunctoriality as Products
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as ProductFrames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as Identity
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductPairingComparisons as Pairing

module At {Γ Δ A B C D : CAT} (F : MAP A C) (G : MAP B D)
  {f g : MAP Γ A} (α : MorphismExpression f g) (h : MAP Δ B) where
  original = restrict-expression α (pr₁ {Γ} {Δ})
  constant = identity-expression (h ∘ pr₂ {Γ} {Δ})
  module Product = Products.At 𝒯 M ℱ P I E S F G original constant

  module Endpoint (k : MAP Γ A) where
    first : (F ∘ (k ∘ pr₁ {Γ} {Δ})) =₁ ((F ∘ k) ∘ pr₁)
    first = (comp-assoc pr₁ k F) ⁻¹
    second : (G ∘ (h ∘ pr₂ {Γ} {Δ})) =₁ ((G ∘ h) ∘ pr₂)
    second = (comp-assoc pr₂ h G) ⁻¹
    module Pair = Pairing.ProductPair 𝒯 M F G (k ∘ pr₁) (h ∘ pr₂) first second
    normalization : (pair-cong first second ∙ productMap-pair F G (k ∘ pr₁) (h ∘ pr₂)) =₂ productMap-comp k F h G
    normalization = Pair.normalization

  module Source = Endpoint f
  module Target = Endpoint g
  module Paired = ProductFrames.At 𝒯 M ℱ I (post-expression F original) (post-expression G constant)
    Source.first Target.first Source.second Target.second

  abstract
    first : ExpressionIso (retarget-expression (post-expression F original) Source.first Target.first)
      (restrict-expression (post-expression F α) pr₁)
    first = expressionIso-compose
      (retarget-cancel (restrict-expression (post-expression F α) pr₁) (comp-assoc pr₁ f F) (comp-assoc pr₁ g F))
      (retarget-expressionIso (expressionIso-inverse (restrict-post F α pr₁)) Source.first Target.first)

    second : ExpressionIso (retarget-expression (post-expression G constant) Source.second Target.second)
      (identity-expression ((G ∘ h) ∘ pr₂ {Γ} {Δ}))
    second = expressionIso-compose (Identity.At.comparison 𝒯 M ℱ P I E Source.second)
      (retarget-expressionIso (post-identity G (h ∘ pr₂)) Source.second Target.second)

    value : ExpressionIso (retarget-expression (post-expression (productMap F G) (external-product α h))
        (productMap-comp f F h G) (productMap-comp g F h G))
      (external-product (post-expression F α) (G ∘ h))
    value = expressionIso-compose (pair-expression-cong first second)
      (expressionIso-compose Paired.value
        (expressionIso-compose (retarget-expressionIso Product.value
            (pair-cong Source.first Source.second) (pair-cong Target.first Target.second))
          (expressionIso-compose
            (expressionIso-inverse (retarget-assoc (post-expression (productMap F G) (external-product α h))
              (productMap-pair F G (f ∘ pr₁) (h ∘ pr₂)) (productMap-pair F G (g ∘ pr₁) (h ∘ pr₂))
              (pair-cong Source.first Source.second) (pair-cong Target.first Target.second)))
            (retarget-cong (post-expression (productMap F G) (external-product α h))
              (Source.normalization ⁻¹) (Target.normalization ⁻¹)))))
```
