# Composition in a product

Apply the two projections, use preservation of composition, and reflect
the resulting endpoint-preserving comparisons. The product beta frames
are displayed explicitly in each projected comparison.

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

module SCT.VolumeI.Chapter02.Section02.ProductComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.PostcompositionPresentations 𝒯 M ℱ P I E S using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.ProductExpressionReflection 𝒯 M ℱ I using (product-expression-reflect)
open import SCT.VolumeI.Chapter02.Section02.ProductExpressions 𝒯 M ℱ I using (pair-expression)
import SCT.VolumeI.Chapter02.Section02.ProductExpressions as Pairing
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)

retarget-reflect : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
  {f g : MorphismExpression x y} (p : x =₁ x′) (q : y =₁ y′) →
  ExpressionIso (retarget-expression f p q) (retarget-expression g p q) → ExpressionIso f g
retarget-reflect {g = g} p q α = record { comparison = A.comparison
  ; source-compatible = cancel-left-reflect p
      (A.source-compatible ∙ (isoComp-assoc-at p (MorphismExpression.source-frame g) (ev₀ ◁ A.comparison)) ⁻¹)
  ; target-compatible = cancel-left-reflect q
      (A.target-compatible ∙ (isoComp-assoc-at q (MorphismExpression.target-frame g) (ev₁ ◁ A.comparison)) ⁻¹) }
  where module A = ExpressionIso α

module At {Γ C D : CAT} {x₁ y₁ z₁ : MAP Γ C} {x₂ y₂ z₂ : MAP Γ D}
  (f₁ : MorphismExpression x₁ y₁) (g₁ : MorphismExpression y₁ z₁)
  (f₂ : MorphismExpression x₂ y₂) (g₂ : MorphismExpression y₂ z₂) where
  module First = Pairing.At 𝒯 M ℱ I f₁ f₂
  module Second = Pairing.At 𝒯 M ℱ I g₁ g₂
  module Long = Pairing.At 𝒯 M ℱ I (compose-expression f₁ g₁) (compose-expression f₂ g₂)
  f = pair-expression f₁ f₂
  g = pair-expression g₁ g₂
  h = pair-expression (compose-expression f₁ g₁) (compose-expression f₂ g₂)

  module Projection {Y : CAT} (π : MAP (C × D) Y) {x y z : MAP Γ Y}
    (p : (π ∘ pair x₁ x₂) =₁ x) (q : (π ∘ pair y₁ y₂) =₁ y) (r : (π ∘ pair z₁ z₂) =₁ z)
    (u : MorphismExpression x y) (v : MorphismExpression y z)
    (first : ExpressionIso (retarget-expression (post-expression π f) p q) u)
    (second : ExpressionIso (retarget-expression (post-expression π g) q r) v)
    (long : ExpressionIso (retarget-expression (post-expression π h) p r) (compose-expression u v)) where
    comparison : ExpressionIso (post-expression π (compose-expression f g)) (post-expression π h)
    comparison = retarget-reflect p r
      (expressionIso-compose (expressionIso-inverse long)
        (expressionIso-compose (compose-expression-cong first second)
          (expressionIso-inverse
            (expressionIso-compose (retarget-expressionIso (post-composition π f g) p r)
              (retarget-composition (post-expression π f) (post-expression π g) p q r)))))

  comparison : ExpressionIso (compose-expression f g) h
  comparison = product-expression-reflect
    (Projection.comparison pr₁ (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂) (pair-β₁ z₁ z₂)
      f₁ g₁ First.first-projection Second.first-projection Long.first-projection)
    (Projection.comparison pr₂ (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂) (pair-β₂ z₁ z₂)
      f₂ g₂ First.second-projection Second.second-projection Long.second-projection)

product-composition : {Γ C D : CAT} {x₁ y₁ z₁ : MAP Γ C} {x₂ y₂ z₂ : MAP Γ D}
  (f₁ : MorphismExpression x₁ y₁) (g₁ : MorphismExpression y₁ z₁)
  (f₂ : MorphismExpression x₂ y₂) (g₂ : MorphismExpression y₂ z₂) →
  ExpressionIso (compose-expression (pair-expression f₁ f₂) (pair-expression g₁ g₂))
    (pair-expression (compose-expression f₁ g₁) (compose-expression f₂ g₂))
product-composition = At.comparison
```

Pairing also preserves identifications of both factors, with the same
product endpoint frames.

```agda
pair-expression-cong : {Γ C D : CAT} {x₁ y₁ : MAP Γ C} {x₂ y₂ : MAP Γ D}
  {f f′ : MorphismExpression x₁ y₁} {g g′ : MorphismExpression x₂ y₂} →
  ExpressionIso f f′ → ExpressionIso g g′ →
  ExpressionIso (pair-expression f g) (pair-expression f′ g′)
pair-expression-cong {x₁ = x₁} {y₁} {x₂} {y₂} {f} {f′} {g} {g′} α β = product-expression-reflect
  (retarget-reflect (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂)
    (expressionIso-compose (expressionIso-inverse New.first-projection)
      (expressionIso-compose α Old.first-projection)))
  (retarget-reflect (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂)
    (expressionIso-compose (expressionIso-inverse New.second-projection)
      (expressionIso-compose β Old.second-projection)))
  where
  module Old = Pairing.At 𝒯 M ℱ I f g
  module New = Pairing.At 𝒯 M ℱ I f′ g′
```
