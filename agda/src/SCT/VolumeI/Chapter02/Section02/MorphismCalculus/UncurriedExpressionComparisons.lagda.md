# Uncurrying framed expression comparisons

An endpoint-preserving expression comparison gives a comparison of the
uncurried diagrams with both endpoint equations. Naturality of evaluation
transports the frames across uncurrying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedExpressionComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ
  using (module Evaluation)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module UncurryComparison {Γ C : CAT} {x y : MAP Γ C} {f g : MorphismExpression x y} (ξ : ExpressionIso f g) where
  module F = MorphismExpression f
  module G = MorphismExpression g
  module X = ExpressionIso ξ
  underlying = funUncurryIso X.comparison

  module Endpoint (z : Obj-abs [1]) {v : MAP Γ C}
    (a₀ : (evaluate z ∘ F.arrow) =₁ v) (a₁ : (evaluate z ∘ G.arrow) =₁ v)
    (compatible : (a₁ ∙ (evaluate z ◁ X.comparison)) =₂ a₀) where
    Q₀ = evaluate-uncurry z F.arrow
    Q₁ = evaluate-uncurry z G.arrow
    e = evaluate z ◁ X.comparison
    d = underlying ▷ insert z

    abstract
      comparison : ((a₁ ∙ Q₁ ⁻¹) ∙ d) =₂ (a₀ ∙ Q₀ ⁻¹)
      comparison = isoComp-cong compatible (idIso (Q₀ ⁻¹)) ∙
        (isoComp-assoc-at a₁ e (Q₀ ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso a₁) (move-square Q₁ e d Q₀ (Evaluation.natural z X.comparison)) ∙
        isoComp-assoc-at a₁ (Q₁ ⁻¹) d

  source-compatible : (((G.source-frame ∙ (evaluate-uncurry zero G.arrow) ⁻¹)) ∙ (underlying ▷ insert zero)) =₂
    (F.source-frame ∙ (evaluate-uncurry zero F.arrow) ⁻¹)
  source-compatible = Endpoint.comparison zero F.source-frame G.source-frame X.source-compatible

  target-compatible : (((G.target-frame ∙ (evaluate-uncurry one G.arrow) ⁻¹)) ∙ (underlying ▷ insert one)) =₂
    (F.target-frame ∙ (evaluate-uncurry one F.arrow) ⁻¹)
  target-compatible = Endpoint.comparison one F.target-frame G.target-frame X.target-compatible
```
