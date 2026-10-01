# The diagram of a paired transformation

The uncurried diagram of a paired expression is the pair of the two
uncurried diagrams. Both endpoint equations follow from the full
projection comparisons of the chosen paired expression.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
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

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
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
    using (arrow; source-frame; target-frame)
  module G = MorphismExpression g
    using (arrow; source-frame; target-frame)
  -- Restructured: no module instantiations except record modules; results of
  -- other modules are used through private abbreviations.
  private
    pair-arrow = Pairing.At.arrow 𝒯 M ℱ I f g
    pair-expression = Pairing.At.expression-pair 𝒯 M ℱ I f g
    first-arrow = Pairing.At.first-arrow 𝒯 M ℱ I f g
    second-arrow = Pairing.At.second-arrow 𝒯 M ℱ I f g
    first-comparison = Post.At.comparison 𝒯 M ℱ P I E pr₁ pair-expression f
      (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂) (Pairing.At.first-projection 𝒯 M ℱ I f g)
    second-comparison = Post.At.comparison 𝒯 M ℱ P I E pr₂ pair-expression g
      (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂) (Pairing.At.second-projection 𝒯 M ℱ I f g)
  H = funUncurry F.arrow
  K = funUncurry G.arrow
  original = funUncurry pair-arrow
  diagram = pair H K
  first-image = (pair-β₁ H K) ⁻¹ ∙ first-comparison
  second-image = (pair-β₂ H K) ⁻¹ ∙ second-comparison
  comparison : original =₁ diagram
  comparison = pair-iso first-image second-image

  first-triangle : (pair-β₁ H K ∙ (pr₁ ◁ comparison)) =₂ first-comparison
  first-triangle = cancel-inverse (pair-β₁ H K) first-comparison ∙
    isoComp-cong (idIso (pair-β₁ H K)) (pair-iso-β₁ first-image second-image)
  second-triangle : (pair-β₂ H K ∙ (pr₂ ◁ comparison)) =₂ second-comparison
  second-triangle = cancel-inverse (pair-β₂ H K) second-comparison ∙
    isoComp-cong (idIso (pair-β₂ H K)) (pair-iso-β₂ first-image second-image)

  module Endpoint (z : Obj-abs [1]) {x : MAP Γ C} {y : MAP Γ D}
    (p : (evaluate z ∘ F.arrow) =₁ x) (q : (evaluate z ∘ G.arrow) =₁ y)
    (r : (evaluate z ∘ pair-arrow) =₁ pair x y)
    (first : (p ∙ (evaluate z ◁ first-arrow)) =₂ (pair-β₁ x y ∙ post-boundary z pr₁ pair-arrow r))
    (second : (q ∙ (evaluate z ◁ second-arrow)) =₂ (pair-β₂ x y ∙ post-boundary z pr₂ pair-arrow r)) where
    i = insert {X = Γ} z
    frontF = p ∙ (evaluate-uncurry z F.arrow) ⁻¹
    frontG = q ∙ (evaluate-uncurry z G.arrow) ⁻¹
    front = r ∙ (evaluate-uncurry z pair-arrow) ⁻¹
    frame : (diagram ∘ i) =₁ pair x y
    frame = pair-cong frontF frontG ∙ pair-pre H K i

    -- The projection lemmas are functions rather than a parameterized local
    -- module: Agda 2.8 spends most of this module's time on the section
    -- telescope of such a module (in dead-code analysis), not on the proofs.
    private
      δ = comparison ▷ i
      abstract
        projection-restricted : {Y : CAT} (π : MAP (C × D) Y) (h : MAP (Γ × [1]) Y)
          (d : (π ∘ original) =₁ h) (b : (π ∘ diagram) =₁ h)
          (image : (b ∙ (π ◁ comparison)) =₂ d) →
          (((b ▷ i) ∙ (comp-assoc i diagram π) ⁻¹) ∙ (π ◁ δ)) =₂
            ((d ▷ i) ∙ (comp-assoc i original π) ⁻¹)
        projection-restricted π h d b image =
          isoComp-unitˡ-at ((d ▷ i) ∙ (comp-assoc i original π) ⁻¹) ∙
          isoComp-cong (preWhisker-idIso h i) (idIso ((d ▷ i) ∙ (comp-assoc i original π) ⁻¹)) ∙
          pre-square-projection π comparison (idIso h) d b i
            ((isoComp-unitˡ-at d) ⁻¹ ∙ image)

        projection-frame-image : {Y : CAT} (π : MAP (C × D) Y) (h : MAP (Γ × [1]) Y)
          (v : MAP Γ Y) (b : (π ∘ diagram) =₁ h)
          (e : (π ∘ pair x y) =₁ v) (k : (π ∘ pair (H ∘ i) (K ∘ i)) =₁ (h ∘ i))
          (a₀ : (h ∘ i) =₁ v)
          (pair-frame : (e ∙ (π ◁ pair-cong frontF frontG)) =₂ (a₀ ∙ k))
          (pre-frame : (k ∙ (π ◁ pair-pre H K i)) =₂ ((b ▷ i) ∙ (comp-assoc i diagram π) ⁻¹)) →
          (e ∙ (π ◁ frame)) =₂ (a₀ ∙ ((b ▷ i) ∙ (comp-assoc i diagram π) ⁻¹))
        projection-frame-image π h v b e k a₀ pair-frame pre-frame =
          isoComp-cong (idIso a₀) pre-frame ∙
          isoComp-assoc-at a₀ k (π ◁ pair-pre H K i) ∙
          isoComp-cong pair-frame (idIso (π ◁ pair-pre H K i)) ∙
          (isoComp-assoc-at e (π ◁ pair-cong frontF frontG) (π ◁ pair-pre H K i)) ⁻¹ ∙
          isoComp-cong (idIso e) (postWhisker-isoComp-at π (pair-cong frontF frontG) (pair-pre H K i))

        projection-compatible : {Y : CAT} (π : MAP (C × D) Y) (h : MAP (Γ × [1]) Y)
          (v : MAP Γ Y) (d : (π ∘ original) =₁ h) (b : (π ∘ diagram) =₁ h)
          (e : (π ∘ pair x y) =₁ v) (k : (π ∘ pair (H ∘ i) (K ∘ i)) =₁ (h ∘ i))
          (a₀ : (h ∘ i) =₁ v)
          (image : (b ∙ (π ◁ comparison)) =₂ d)
          (pair-frame : (e ∙ (π ◁ pair-cong frontF frontG)) =₂ (a₀ ∙ k))
          (pre-frame : (k ∙ (π ◁ pair-pre H K i)) =₂ ((b ▷ i) ∙ (comp-assoc i diagram π) ⁻¹))
          (given : (a₀ ∙ (d ▷ i)) =₂ ((e ∙ (π ◁ front)) ∙ comp-assoc i original π)) →
          (π ◁ (frame ∙ δ)) =₂ (π ◁ front)
        projection-compatible π h v d b e k a₀ image pair-frame pre-frame given =
          cancel-left-reflect e
            (cancel-right (comp-assoc i original π) (e ∙ (π ◁ front)) ∙
              isoComp-cong given (idIso ((comp-assoc i original π) ⁻¹)) ∙
              (isoComp-assoc-at a₀ (d ▷ i) ((comp-assoc i original π) ⁻¹)) ⁻¹ ∙
              isoComp-cong (idIso a₀) (projection-restricted π h d b image) ∙
              isoComp-assoc-at a₀ ((b ▷ i) ∙ (comp-assoc i diagram π) ⁻¹) (π ◁ δ) ∙
              isoComp-cong (projection-frame-image π h v b e k a₀ pair-frame pre-frame) (idIso (π ◁ δ)) ∙
              (isoComp-assoc-at e (π ◁ frame) (π ◁ δ)) ⁻¹ ∙
              isoComp-cong (idIso e) (postWhisker-isoComp-at π frame δ))

    compatible : (frame ∙ (comparison ▷ i)) =₂ front
    compatible = pair-iso-extensionality
      (projection-compatible pr₁ H x first-comparison (pair-β₁ H K)
        (pair-β₁ x y) (pair-β₁ (H ∘ i) (K ∘ i)) frontF first-triangle
        (pair-cong-triangle₁ frontF frontG) (pair-pre-triangle₁ H K i)
        (Post.At.Endpoint.compatible 𝒯 M ℱ P I E pr₁ pair-expression f
          (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂) (Pairing.At.first-projection 𝒯 M ℱ I f g)
          z r p (pair-β₁ x y) first))
      (projection-compatible pr₂ K y second-comparison (pair-β₂ H K)
        (pair-β₂ x y) (pair-β₂ (H ∘ i) (K ∘ i)) frontG second-triangle
        (pair-cong-triangle₂ frontF frontG) (pair-pre-triangle₂ H K i)
        (Post.At.Endpoint.compatible 𝒯 M ℱ P I E pr₂ pair-expression g
          (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂) (Pairing.At.second-projection 𝒯 M ℱ I f g)
          z r q (pair-β₂ x y) second))

  -- The two endpoint instances, as plain modules of direct calls (only the
  -- names used by ExpressionDiagramPresentations).
  module Source where
    private
      r = Pairing.At.Source.frame 𝒯 M ℱ I f g
      first = Pairing.At.Source.first-compatible 𝒯 M ℱ I f g ⁻¹
      second = Pairing.At.Source.second-compatible 𝒯 M ℱ I f g ⁻¹
    frontF = Endpoint.frontF zero F.source-frame G.source-frame r first second
    frontG = Endpoint.frontG zero F.source-frame G.source-frame r first second
    front = Endpoint.front zero F.source-frame G.source-frame r first second
    frame = Endpoint.frame zero F.source-frame G.source-frame r first second
    compatible = Endpoint.compatible zero F.source-frame G.source-frame r first second
  module Target where
    private
      r = Pairing.At.Target.frame 𝒯 M ℱ I f g
      first = Pairing.At.Target.first-compatible 𝒯 M ℱ I f g ⁻¹
      second = Pairing.At.Target.second-compatible 𝒯 M ℱ I f g ⁻¹
    frontF = Endpoint.frontF one F.target-frame G.target-frame r first second
    frontG = Endpoint.frontG one F.target-frame G.target-frame r first second
    front = Endpoint.front one F.target-frame G.target-frame r first second
    frame = Endpoint.frame one F.target-frame G.target-frame r first second
    compatible = Endpoint.compatible one F.target-frame G.target-frame r first second
```
