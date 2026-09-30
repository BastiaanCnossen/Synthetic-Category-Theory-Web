# Restriction of an external product transformation

Restricting along a product map restricts the transformation in the first
coordinate and composes the fixed functor in the second. Both endpoint
comparisons are the existing product-functor compositors.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as ProductFrames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionRestriction as Products
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionSquare as Square
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdentityRestriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdentityFrames

module At {Γ Δ Ω Θ A B : CAT} {f g : MAP Γ A} (α : MorphismExpression f g)
  (h : MAP Δ B) (r : MAP Ω Γ) (s : MAP Θ Δ) where
  σ : MAP (Ω × Θ) (Γ × Δ)
  σ = productMap r s
  original = restrict-expression α (pr₁ {Γ} {Δ})
  constant = identity-expression (h ∘ pr₂ {Γ} {Δ})
  module Product = Products.At 𝒯 M ℱ P I E S original constant σ
  module First = Square.At 𝒯 M ℱ I α (pr₁ {Γ} {Δ}) σ r (pr₁ {Ω} {Θ})
    (pair-β₁ (r ∘ pr₁) (s ∘ pr₂))
  second : ((h ∘ pr₂) ∘ σ) =₁ ((h ∘ s) ∘ pr₂ {Ω} {Θ})
  second = (comp-assoc pr₂ s h) ⁻¹ ∙
    ((h ◁ pair-β₂ (r ∘ pr₁) (s ∘ pr₂)) ∙ comp-assoc σ pr₂ h)
  module Paired = ProductFrames.At 𝒯 M ℱ I (restrict-expression original σ) (restrict-expression constant σ)
    First.source-change First.target-change second second

  abstract
    second-comparison : ExpressionIso (retarget-expression (restrict-expression constant σ) second second)
      (identity-expression ((h ∘ s) ∘ pr₂ {Ω} {Θ}))
    second-comparison = expressionIso-compose (IdentityFrames.At.comparison 𝒯 M ℱ P I E second)
      (retarget-expressionIso (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E (h ∘ pr₂) σ) second second)

    value : ExpressionIso (retarget-expression (restrict-expression (external-product α h) σ)
        (productMap-comp r f s h) (productMap-comp r g s h))
      (external-product (restrict-expression α r) (h ∘ s))
    value = expressionIso-compose (pair-expression-cong First.value second-comparison)
      (expressionIso-compose Paired.value
        (expressionIso-compose (retarget-expressionIso Product.value
            (pair-cong First.source-change second) (pair-cong First.target-change second))
          (expressionIso-inverse (retarget-assoc (restrict-expression (external-product α h) σ)
            (pair-pre (f ∘ pr₁) (h ∘ pr₂) σ) (pair-pre (g ∘ pr₁) (h ∘ pr₂) σ)
            (pair-cong First.source-change second) (pair-cong First.target-change second)))))
```
