# Pairing with changed endpoint frames

Changing the endpoints of each factor changes the paired endpoints by
the paired identifications. The proof projects to each factor and uses
the specified product beta comparisons throughout.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget; retarget-assoc; retarget-cong; retarget-cancel)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions as Products
open Products 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionReflection 𝒯 M ℱ I
  using (product-expression-reflect)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₁; pair-cong-triangle₂)

private
  reflect-retarget : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
    {α β : MorphismExpression x y} (p : x =₁ x′) (q : y =₁ y′) →
    ExpressionIso (retarget-expression α p q) (retarget-expression β p q) → ExpressionIso α β
  reflect-retarget {α = α} {β} p q ξ = expressionIso-compose (retarget-cancel β p q)
    (expressionIso-compose (retarget-expressionIso ξ (p ⁻¹) (q ⁻¹))
      (expressionIso-inverse (retarget-cancel α p q)))

module At {Γ C D : CAT} {x y x′ y′ : MAP Γ C} {u v u′ v′ : MAP Γ D}
  (α : MorphismExpression x y) (β : MorphismExpression u v)
  (p : x =₁ x′) (q : y =₁ y′) (r : u =₁ u′) (s : v =₁ v′) where
  module Old = Products.At 𝒯 M ℱ I α β
  module New = Products.At 𝒯 M ℱ I (retarget-expression α p q) (retarget-expression β r s)
  source-change = pair-cong p r
  target-change = pair-cong q s
  old = pair-expression α β
  new = pair-expression (retarget-expression α p q) (retarget-expression β r s)
  changed = retarget-expression old source-change target-change

  module Projection {Y : CAT} (π : MAP (C × D) Y) {a b a′ b′ : MAP Γ Y}
    (τ : MorphismExpression a b) (k : a =₁ a′) (l : b =₁ b′)
    (b₀ : (π ∘ pair x u) =₁ a) (b₁ : (π ∘ pair y v) =₁ b)
    (c₀ : (π ∘ pair x′ u′) =₁ a′) (c₁ : (π ∘ pair y′ v′) =₁ b′)
    (first : ExpressionIso (retarget-expression (post-expression π old) b₀ b₁) τ)
    (second : ExpressionIso (retarget-expression (post-expression π new) c₀ c₁)
      (retarget-expression τ k l))
    (source : (c₀ ∙ (π ◁ source-change)) =₂ (k ∙ b₀))
    (target : (c₁ ∙ (π ◁ target-change)) =₂ (l ∙ b₁)) where
    abstract
      normalized : ExpressionIso (retarget-expression (post-expression π changed) c₀ c₁)
        (retarget-expression τ k l)
      normalized = expressionIso-compose (retarget-expressionIso first k l)
        (expressionIso-compose (expressionIso-inverse (retarget-assoc (post-expression π old) b₀ b₁ k l))
          (expressionIso-compose (retarget-cong (post-expression π old) source target)
            (expressionIso-compose (retarget-assoc (post-expression π old)
                (π ◁ source-change) (π ◁ target-change) c₀ c₁)
              (retarget-expressionIso (post-retarget π old source-change target-change) c₀ c₁))))

      comparison : ExpressionIso (post-expression π changed) (post-expression π new)
      comparison = reflect-retarget c₀ c₁ (expressionIso-compose (expressionIso-inverse second) normalized)

  value : ExpressionIso changed new
  value = product-expression-reflect
    (Projection.comparison pr₁ α p q (pair-β₁ x u) (pair-β₁ y v) (pair-β₁ x′ u′) (pair-β₁ y′ v′)
      Old.first-projection New.first-projection (pair-cong-triangle₁ p r) (pair-cong-triangle₁ q s))
    (Projection.comparison pr₂ β r s (pair-β₂ x u) (pair-β₂ y v) (pair-β₂ x′ u′) (pair-β₂ y′ v′)
      Old.second-projection New.second-projection (pair-cong-triangle₂ p r) (pair-cong-triangle₂ q s))
```
