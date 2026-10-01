# Pairing morphism expressions

Lift the pair of arrow diagrams through the functor-product equivalence,
then pair their endpoint frames. The projection comparisons retain the
product beta identifications at the source and target.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-boundary-normal)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section07.FunctorProducts as Products
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {Γ C D : CAT} {x₁ y₁ : MAP Γ C} {x₂ y₂ : MAP Γ D}
  (f : MorphismExpression x₁ y₁) (g : MorphismExpression x₂ y₂) where
  module F = MorphismExpression f
    using (arrow; source-frame; target-frame)
  module G = MorphismExpression g
    using (arrow; source-frame; target-frame)
  module Product = Products.ProductComparison 𝒯 M ℱ [1] C D
    using (forward; forward-isEquiv)
  chosen = equiv-lift Product.forward-isEquiv (pair F.arrow G.arrow)
  arrow : MAP Γ (Ar (C × D))
  arrow = FunctorLift.lift chosen
  comparison : (Product.forward ∘ arrow) =₁ pair F.arrow G.arrow
  comparison = FunctorLift.comparison chosen
  first-arrow : (funPost pr₁ ∘ arrow) =₁ F.arrow
  first-arrow = pair-β₁ F.arrow G.arrow ∙ ((pr₁ ◁ comparison) ∙
    (comp-assoc arrow Product.forward pr₁ ∙ ((pair-β₁ (funPost pr₁) (funPost pr₂) ▷ arrow) ⁻¹)))
  second-arrow : (funPost pr₂ ∘ arrow) =₁ G.arrow
  second-arrow = pair-β₂ F.arrow G.arrow ∙ ((pr₂ ◁ comparison) ∙
    (comp-assoc arrow Product.forward pr₂ ∙ ((pair-β₂ (funPost pr₁) (funPost pr₂) ▷ arrow) ⁻¹)))

  module Endpoint (v : Obj-abs [1]) {x : MAP Γ C} {y : MAP Γ D}
    (p : (evaluate v ∘ F.arrow) =₁ x) (q : (evaluate v ∘ G.arrow) =₁ y) where
    first = (p ∙ (evaluate v ◁ first-arrow)) ∙ (evaluate-post-at v pr₁ arrow) ⁻¹
    second = (q ∙ (evaluate v ◁ second-arrow)) ∙ (evaluate-post-at v pr₂ arrow) ⁻¹
    frame : (evaluate v ∘ arrow) =₁ pair x y
    frame = pair-iso ((pair-β₁ x y) ⁻¹ ∙ first) ((pair-β₂ x y) ⁻¹ ∙ second)

    module Projection {Y : CAT} (π : MAP (C × D) Y) (z : MAP Γ Y)
      (b : (π ∘ pair x y) =₁ z) (k : MAP Γ (Ar Y))
      (α : (funPost π ∘ arrow) =₁ k) (r : (evaluate v ∘ k) =₁ z)
      (image : (π ◁ frame) =₂ (b ⁻¹ ∙ ((r ∙ (evaluate v ◁ α)) ∙ (evaluate-post-at v π arrow) ⁻¹))) where
      R = evaluate-post-at v π arrow
      L = (r ∙ (evaluate v ◁ α)) ∙ R ⁻¹
      abstract
        normal : (b ∙ post-boundary v π arrow frame) =₂ (r ∙ (evaluate v ◁ α))
        normal = cancel-inverse-tail (r ∙ (evaluate v ◁ α)) R ∙
          isoComp-cong (cancel-inverse b L ∙ isoComp-cong (idIso b) image) (idIso R) ∙
          (isoComp-assoc-at b (π ◁ frame) R) ⁻¹ ∙
          isoComp-cong (idIso b) (post-boundary-normal v π arrow frame)

    first-compatible = Projection.normal pr₁ x (pair-β₁ x y) F.arrow first-arrow p
      (pair-iso-β₁ ((pair-β₁ x y) ⁻¹ ∙ first) ((pair-β₂ x y) ⁻¹ ∙ second))
    second-compatible = Projection.normal pr₂ y (pair-β₂ x y) G.arrow second-arrow q
      (pair-iso-β₂ ((pair-β₁ x y) ⁻¹ ∙ first) ((pair-β₂ x y) ⁻¹ ∙ second))

  module Source = Endpoint zero F.source-frame G.source-frame
  module Target = Endpoint one F.target-frame G.target-frame
  expression-pair : MorphismExpression (pair x₁ x₂) (pair y₁ y₂)
  expression-pair = record { arrow = arrow ; source-frame = Source.frame ; target-frame = Target.frame }

  first-projection : ExpressionIso
    (retarget-expression (post-expression pr₁ expression-pair) (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂)) f
  first-projection = record { comparison = first-arrow
    ; source-compatible = Source.first-compatible ⁻¹ ; target-compatible = Target.first-compatible ⁻¹ }
  second-projection : ExpressionIso
    (retarget-expression (post-expression pr₂ expression-pair) (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂)) g
  second-projection = record { comparison = second-arrow
    ; source-compatible = Source.second-compatible ⁻¹ ; target-compatible = Target.second-compatible ⁻¹ }

pair-expression : {Γ C D : CAT} {x₁ y₁ : MAP Γ C} {x₂ y₂ : MAP Γ D} →
  MorphismExpression x₁ y₁ → MorphismExpression x₂ y₂ → MorphismExpression (pair x₁ x₂) (pair y₁ y₂)
pair-expression = At.expression-pair
```
