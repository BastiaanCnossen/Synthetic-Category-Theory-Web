# External products with an identity transformation

A transformation on one factor pairs with the identity transformation of
a functor on the other factor. The endpoint changes are the specified
product-functor identifications. This construction is used to compare
the two coordinates in precomposition and evaluation.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (restrict-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (pair-expression-cong)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames as ProductFrames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as Identity

external-product : {Γ Δ A B : CAT} {f g : MAP Γ A} → MorphismExpression f g →
  (h : MAP Δ B) → MorphismExpression (productMap f h) (productMap g h)
external-product α h = pair-expression (restrict-expression α pr₁) (identity-expression (h ∘ pr₂))

external-product-cong : {Γ Δ A B : CAT} {f g : MAP Γ A} {α β : MorphismExpression f g} →
  ExpressionIso α β → (h : MAP Δ B) → ExpressionIso (external-product α h) (external-product β h)
external-product-cong ξ h = pair-expression-cong (restrict-expressionIso ξ pr₁)
  (expressionIso-id (identity-expression (h ∘ pr₂)))

module Frames {Γ Δ A B : CAT} {f g f′ g′ : MAP Γ A}
  (α : MorphismExpression f g) (p : f =₁ f′) (q : g =₁ g′)
  {h k : MAP Δ B} (ρ : h =₁ k) where
  module Paired = ProductFrames.At 𝒯 M ℱ I (restrict-expression α (pr₁ {Γ} {Δ})) (identity-expression (h ∘ pr₂))
    (p ▷ pr₁) (q ▷ pr₁) (ρ ▷ pr₂) (ρ ▷ pr₂)
    using (value)

  abstract
    value : ExpressionIso (retarget-expression (external-product α h) (productMap-cong p ρ) (productMap-cong q ρ))
      (external-product (retarget-expression α p q) k)
    value = expressionIso-compose
      (pair-expression-cong (expressionIso-inverse (restrict-retarget α p q pr₁))
        (Identity.At.comparison 𝒯 M ℱ P I E (ρ ▷ pr₂))) Paired.value

    map : {β : MorphismExpression f′ g′} → ExpressionIso (retarget-expression α p q) β →
      ExpressionIso (retarget-expression (external-product α h) (productMap-cong p ρ) (productMap-cong q ρ))
        (external-product β k)
    map ξ = expressionIso-compose (external-product-cong ξ k) value
```
