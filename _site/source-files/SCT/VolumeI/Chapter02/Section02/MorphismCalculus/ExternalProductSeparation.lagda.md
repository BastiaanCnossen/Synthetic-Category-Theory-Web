# Separating the two coordinates of an external product

Changing the fixed second coordinate before or after forming the external
product gives the same transformation. The comparison retains the chosen
`productMap-separate` identification at both endpoints.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductSeparation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; retarget-cancel)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFunctorExpressions 𝒯 M ℱ P I E using (post-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expression-id)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductPostcomposition as Post
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExternalProductRestriction as Restrict
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite)

module At {Γ A B C : CAT} {f g : MAP Γ A} (α : MorphismExpression f g) (r : MAP B C) where
  left = post-expression (productMap (id A) r) (external-product α (id B))
  right = restrict-expression (external-product α (id C)) (productMap (id Γ) r)
  common = external-product α r
  module Left = Post.At 𝒯 M ℱ P I E S (id A) r α (id B)
  module Right = Restrict.At 𝒯 M ℱ P I E S α (id C) (id Γ) r
  module LeftFrames = Frames (post-expression (id A) α) (comp-unitˡ f) (comp-unitˡ g) (comp-unitʳ r)
  module RightFrames = Frames (restrict-expression α (id Γ)) (comp-unitʳ f) (comp-unitʳ g) (comp-unitˡ r)

  module Endpoint (k : MAP Γ A) where
    left-unit = productMap-cong (comp-unitˡ k) (comp-unitʳ r)
    right-unit = productMap-cong (comp-unitʳ k) (comp-unitˡ r)
    left-comp = productMap-comp k (id A) (id B) r
    right-comp = productMap-comp (id Γ) k r (id C)
    left-normal = left-unit ∙ left-comp
    right-normal = right-unit ∙ right-comp

    abstract
      normalization : (right-normal ⁻¹ ∙ left-normal) =₂ productMap-separate k r
      normalization = isoComp-assoc-at (right-comp ⁻¹) (right-unit ⁻¹) left-normal ∙
        isoComp-cong (inverse-composite right-unit right-comp) (idIso left-normal)

  module Source = Endpoint f
  module Target = Endpoint g

  abstract
    left-comparison : ExpressionIso (retarget-expression left Source.left-normal Target.left-normal) common
    left-comparison = expressionIso-compose (LeftFrames.map (post-id α))
      (expressionIso-compose (retarget-expressionIso Left.value Source.left-unit Target.left-unit)
        (expressionIso-inverse (retarget-assoc left Source.left-comp Target.left-comp Source.left-unit Target.left-unit)))

    right-comparison : ExpressionIso (retarget-expression right Source.right-normal Target.right-normal) common
    right-comparison = expressionIso-compose (RightFrames.map (restrict-expression-id α))
      (expressionIso-compose (retarget-expressionIso Right.value Source.right-unit Target.right-unit)
        (expressionIso-inverse (retarget-assoc right Source.right-comp Target.right-comp Source.right-unit Target.right-unit)))

    quotient : ExpressionIso (retarget-expression left
        (Source.right-normal ⁻¹ ∙ Source.left-normal) (Target.right-normal ⁻¹ ∙ Target.left-normal)) right
    quotient = expressionIso-compose (retarget-cancel right Source.right-normal Target.right-normal)
      (expressionIso-compose (retarget-expressionIso (expressionIso-inverse right-comparison)
          (Source.right-normal ⁻¹) (Target.right-normal ⁻¹))
        (expressionIso-compose (retarget-expressionIso left-comparison (Source.right-normal ⁻¹) (Target.right-normal ⁻¹))
          (expressionIso-inverse (retarget-assoc left Source.left-normal Target.left-normal
            (Source.right-normal ⁻¹) (Target.right-normal ⁻¹)))))

    value : ExpressionIso (retarget-expression left (productMap-separate f r) (productMap-separate g r)) right
    value = expressionIso-compose quotient
      (retarget-cong left (Source.normalization ⁻¹) (Target.normalization ⁻¹))
```
