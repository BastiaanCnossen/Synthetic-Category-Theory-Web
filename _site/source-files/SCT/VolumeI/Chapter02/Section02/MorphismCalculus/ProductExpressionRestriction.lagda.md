# Restriction of paired transformations

Restriction commutes with pairing after the specified product comparison
at both endpoints. Projection to each factor reduces the claim to the
existing restriction and postcomposition comparisons.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget; retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-post-frames)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (retarget-reflect)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions as Products
open Products 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionReflection 𝒯 M ℱ I
  using (product-expression-reflect)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-triangle₁; pair-pre-triangle₂)

module At {Γ Δ C D : CAT} {x y : MAP Γ C} {u v : MAP Γ D}
  (α : MorphismExpression x y) (β : MorphismExpression u v) (r : MAP Δ Γ) where
  module Old = Products.At 𝒯 M ℱ I α β
  module New = Products.At 𝒯 M ℱ I (restrict-expression α r) (restrict-expression β r)
  old = pair-expression α β
  new = pair-expression (restrict-expression α r) (restrict-expression β r)
  p = pair-pre x u r
  q = pair-pre y v r
  changed = retarget-expression (restrict-expression old r) p q

  module Projection {Y : CAT} (π : MAP (C × D) Y) {a b : MAP Γ Y}
    (τ : MorphismExpression a b)
    (b₀ : (π ∘ pair x u) =₁ a) (b₁ : (π ∘ pair y v) =₁ b)
    (c₀ : (π ∘ pair (x ∘ r) (u ∘ r)) =₁ (a ∘ r))
    (c₁ : (π ∘ pair (y ∘ r) (v ∘ r)) =₁ (b ∘ r))
    (first : ExpressionIso (retarget-expression (post-expression π old) b₀ b₁) τ)
    (second : ExpressionIso (retarget-expression (post-expression π new) c₀ c₁) (restrict-expression τ r))
    (source : (c₀ ∙ (π ◁ p)) =₂ ((b₀ ▷ r) ∙ (comp-assoc r (pair x u) π) ⁻¹))
    (target : (c₁ ∙ (π ◁ q)) =₂ ((b₁ ▷ r) ∙ (comp-assoc r (pair y v) π) ⁻¹)) where
    source-frame = (π ◁ p) ∙ comp-assoc r (pair x u) π
    target-frame = (π ◁ q) ∙ comp-assoc r (pair y v) π

    abstract
      source-normal : (c₀ ∙ source-frame) =₂ (b₀ ▷ r)
      source-normal = cancel-inverse-tail (b₀ ▷ r) (comp-assoc r (pair x u) π) ∙
        isoComp-cong source (idIso (comp-assoc r (pair x u) π)) ∙
        (isoComp-assoc-at c₀ (π ◁ p) (comp-assoc r (pair x u) π)) ⁻¹
      target-normal : (c₁ ∙ target-frame) =₂ (b₁ ▷ r)
      target-normal = cancel-inverse-tail (b₁ ▷ r) (comp-assoc r (pair y v) π) ∙
        isoComp-cong target (idIso (comp-assoc r (pair y v) π)) ∙
        (isoComp-assoc-at c₁ (π ◁ q) (comp-assoc r (pair y v) π)) ⁻¹

      normalized : ExpressionIso (retarget-expression (post-expression π changed) c₀ c₁)
        (restrict-expression τ r)
      normalized = expressionIso-compose (restrict-expressionIso first r)
        (expressionIso-compose (expressionIso-inverse (restrict-retarget (post-expression π old) b₀ b₁ r))
          (expressionIso-compose (retarget-cong (restrict-expression (post-expression π old) r) source-normal target-normal)
            (expressionIso-compose (retarget-assoc (restrict-expression (post-expression π old) r)
                source-frame target-frame c₀ c₁)
              (retarget-expressionIso (expressionIso-inverse (restrict-post-frames π old r p q)) c₀ c₁))))

      comparison : ExpressionIso (post-expression π changed) (post-expression π new)
      comparison = retarget-reflect c₀ c₁ (expressionIso-compose (expressionIso-inverse second) normalized)

  value : ExpressionIso changed new
  value = product-expression-reflect
    (Projection.comparison pr₁ α (pair-β₁ x u) (pair-β₁ y v)
      (pair-β₁ (x ∘ r) (u ∘ r)) (pair-β₁ (y ∘ r) (v ∘ r))
      Old.first-projection New.first-projection (pair-pre-triangle₁ x u r) (pair-pre-triangle₁ y v r))
    (Projection.comparison pr₂ β (pair-β₂ x u) (pair-β₂ y v)
      (pair-β₂ (x ∘ r) (u ∘ r)) (pair-β₂ (y ∘ r) (v ∘ r))
      Old.second-projection New.second-projection (pair-pre-triangle₂ x u r) (pair-pre-triangle₂ y v r))
```
