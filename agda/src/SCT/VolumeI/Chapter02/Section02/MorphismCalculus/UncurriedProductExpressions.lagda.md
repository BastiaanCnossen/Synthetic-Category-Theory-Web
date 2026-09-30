# The diagram of a paired transformation

The uncurried diagram of a paired expression is the pair of the two
uncurried diagrams. Both endpoint equations follow from the full
projection comparisons of the chosen paired expression.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedProductExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions as Pairing
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedPostcompositionComparisons as Post
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pre-square-projection; cancel-left-reflect; cancel-right)
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality; pair-cong-triangle₁; pair-cong-triangle₂;
    pair-pre-triangle₁; pair-pre-triangle₂)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {Γ C D : CAT} {x₁ y₁ : MAP Γ C} {x₂ y₂ : MAP Γ D}
  (f : MorphismExpression x₁ y₁) (g : MorphismExpression x₂ y₂) where
  module F = MorphismExpression f
  module G = MorphismExpression g
  module Pair = Pairing.At 𝒯 M ℱ I f g
  module First = Post.At 𝒯 M ℱ P I E pr₁ Pair.expression-pair f
    (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂) Pair.first-projection
  module Second = Post.At 𝒯 M ℱ P I E pr₂ Pair.expression-pair g
    (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂) Pair.second-projection
  H = funUncurry F.arrow
  K = funUncurry G.arrow
  original = funUncurry Pair.arrow
  diagram = pair H K
  first-image = (pair-β₁ H K) ⁻¹ ∙ First.comparison
  second-image = (pair-β₂ H K) ⁻¹ ∙ Second.comparison
  comparison : original =₁ diagram
  comparison = pair-iso first-image second-image

  first-triangle : (pair-β₁ H K ∙ (pr₁ ◁ comparison)) =₂ First.comparison
  first-triangle = cancel-inverse (pair-β₁ H K) First.comparison ∙
    isoComp-cong (idIso (pair-β₁ H K)) (pair-iso-β₁ first-image second-image)
  second-triangle : (pair-β₂ H K ∙ (pr₂ ◁ comparison)) =₂ Second.comparison
  second-triangle = cancel-inverse (pair-β₂ H K) Second.comparison ∙
    isoComp-cong (idIso (pair-β₂ H K)) (pair-iso-β₂ first-image second-image)

  module Endpoint (z : Obj-abs [1]) {x : MAP Γ C} {y : MAP Γ D}
    (p : (evaluate z ∘ F.arrow) =₁ x) (q : (evaluate z ∘ G.arrow) =₁ y)
    (r : (evaluate z ∘ Pair.arrow) =₁ pair x y)
    (first : (p ∙ (evaluate z ◁ Pair.first-arrow)) =₂ (pair-β₁ x y ∙ post-boundary z pr₁ Pair.arrow r))
    (second : (q ∙ (evaluate z ◁ Pair.second-arrow)) =₂ (pair-β₂ x y ∙ post-boundary z pr₂ Pair.arrow r)) where
    i = insert {X = Γ} z
    frontF = p ∙ (evaluate-uncurry z F.arrow) ⁻¹
    frontG = q ∙ (evaluate-uncurry z G.arrow) ⁻¹
    front = r ∙ (evaluate-uncurry z Pair.arrow) ⁻¹
    frame : (diagram ∘ i) =₁ pair x y
    frame = pair-cong frontF frontG ∙ pair-pre H K i

    module Projection {Y : CAT} (π : MAP (C × D) Y) (h : MAP (Γ × [1]) Y)
      (v : MAP Γ Y) (d : (π ∘ original) =₁ h) (b : (π ∘ diagram) =₁ h)
      (e : (π ∘ pair x y) =₁ v) (k : (π ∘ pair (H ∘ i) (K ∘ i)) =₁ (h ∘ i))
      (a₀ : (h ∘ i) =₁ v)
      (image : (b ∙ (π ◁ comparison)) =₂ d)
      (pair-frame : (e ∙ (π ◁ pair-cong frontF frontG)) =₂ (a₀ ∙ k))
      (pre-frame : (k ∙ (π ◁ pair-pre H K i)) =₂ ((b ▷ i) ∙ (comp-assoc i diagram π) ⁻¹))
      (given : (a₀ ∙ (d ▷ i)) =₂ ((e ∙ (π ◁ front)) ∙ comp-assoc i original π)) where
      R = (b ▷ i) ∙ (comp-assoc i diagram π) ⁻¹
      L = (d ▷ i) ∙ (comp-assoc i original π) ⁻¹
      δ = comparison ▷ i
      abstract
        restricted : (R ∙ (π ◁ δ)) =₂ L
        restricted = isoComp-unitˡ-at L ∙
          isoComp-cong (preWhisker-idIso h i) (idIso L) ∙
          pre-square-projection π comparison (idIso h) d b i
            ((isoComp-unitˡ-at d) ⁻¹ ∙ image)

        frame-image : (e ∙ (π ◁ frame)) =₂ (a₀ ∙ R)
        frame-image = isoComp-cong (idIso a₀) pre-frame ∙
          isoComp-assoc-at a₀ k (π ◁ pair-pre H K i) ∙
          isoComp-cong pair-frame (idIso (π ◁ pair-pre H K i)) ∙
          (isoComp-assoc-at e (π ◁ pair-cong frontF frontG) (π ◁ pair-pre H K i)) ⁻¹ ∙
          isoComp-cong (idIso e) (postWhisker-isoComp-at π (pair-cong frontF frontG) (pair-pre H K i))

        compatible : (π ◁ (frame ∙ δ)) =₂ (π ◁ front)
        compatible = cancel-left-reflect e
          (cancel-right (comp-assoc i original π) (e ∙ (π ◁ front)) ∙
            isoComp-cong given (idIso ((comp-assoc i original π) ⁻¹)) ∙
            (isoComp-assoc-at a₀ (d ▷ i) ((comp-assoc i original π) ⁻¹)) ⁻¹ ∙
            isoComp-cong (idIso a₀) restricted ∙
            isoComp-assoc-at a₀ R (π ◁ δ) ∙
            isoComp-cong frame-image (idIso (π ◁ δ)) ∙
            (isoComp-assoc-at e (π ◁ frame) (π ◁ δ)) ⁻¹ ∙
            isoComp-cong (idIso e) (postWhisker-isoComp-at π frame δ))

    compatible : (frame ∙ (comparison ▷ i)) =₂ front
    compatible = pair-iso-extensionality
      (Projection.compatible pr₁ H x First.comparison (pair-β₁ H K)
        (pair-β₁ x y) (pair-β₁ (H ∘ i) (K ∘ i)) frontF first-triangle
        (pair-cong-triangle₁ frontF frontG) (pair-pre-triangle₁ H K i)
        (First.Endpoint.compatible z r p (pair-β₁ x y) first))
      (Projection.compatible pr₂ K y Second.comparison (pair-β₂ H K)
        (pair-β₂ x y) (pair-β₂ (H ∘ i) (K ∘ i)) frontG second-triangle
        (pair-cong-triangle₂ frontF frontG) (pair-pre-triangle₂ H K i)
        (Second.Endpoint.compatible z r q (pair-β₂ x y) second))

  module Source = Endpoint zero F.source-frame G.source-frame Pair.Source.frame
    (Pair.Source.first-compatible ⁻¹) (Pair.Source.second-compatible ⁻¹)
  module Target = Endpoint one F.target-frame G.target-frame Pair.Target.frame
    (Pair.Target.first-compatible ⁻¹) (Pair.Target.second-compatible ⁻¹)
```
