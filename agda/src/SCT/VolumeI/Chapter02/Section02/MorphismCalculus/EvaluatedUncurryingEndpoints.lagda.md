# Evaluation of the exchanged endpoint triangle

The two coordinate equations assemble into a triangle for product
substitution. Applying evaluation retains its associators and gives the
endpoint equation for the exchanged uncurrying diagram.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EvaluatedUncurryingEndpoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingCoordinateEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionCoordinates as Coordinates
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as Substitution
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.TriangleEvaluation as Evaluation
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
open PC vocabulary terminal products productLaws composition vertical whiskering using (pair-cong-Iso₂)

module At (Γ X C : CAT) (h : MAP Γ (Ar (Fun X C))) where
  module Coordinate = Coordinates.At 𝒯 M ℱ I Γ X C h
    using (H; comparison; diagram; fixed; paired; paired-comparison; permutation; step)
  open Coordinate using (H; step; fixed; permutation; paired; diagram)

  module Endpoint (z : Obj-abs [1]) {f : MAP Γ (Fun X C)}
    (p : (H ∘ insert z) =₁ f) where
    module J = Endpoints.At.Endpoint 𝒯 M ℱ I Γ X C h z p
    module Product = Substitution.Coordinates 𝒯 M X H (insert z)
      using (normalization)
    open J using (i; j; s; κ; first-frame; second-frame)

    u : (paired ∘ permutation) =₁ productMap H (id X)
    u = Coordinate.paired-comparison
    v : (productMap H (id X) ∘ s) =₁ productMap f (id X)
    v = productMap-cong p (idIso (id X)) ∙ slice-comparison H i
    w : (paired ∘ j) =₁ productMap f (id X)
    w = pair-cong first-frame second-frame ∙ pair-pre (H ∘ step) (fixed ∘ pr₁) j
    paired-front : pair ((H ∘ i) ∘ pr₁) fixed =₁ productMap f (id X)
    paired-front = pair-cong (p ▷ pr₁) (idIso fixed)
    normalized-front : paired-front =₂ productMap-cong p (idIso (id X))
    normalized-front = pair-cong-Iso₂ (idIso (p ▷ pr₁))
      ((preWhisker-idIso (id X) (pr₂ {Γ} {X})) ⁻¹)

    abstract
      triangle : (w ∙ ((paired ◁ κ) ∙ comp-assoc s permutation paired)) =₂ (v ∙ (u ▷ s))
      triangle = (isoComp-assoc-at (productMap-cong p (idIso (id X)))
          (slice-comparison H i) (u ▷ s)) ⁻¹ ∙
        isoComp-cong normalized-front
          (isoComp-cong (Product.normalization ⁻¹) (idIso (u ▷ s))) ∙ J.paired-square

    module Applied = Evaluation.At 𝒯 funEval paired permutation s j κ u v w triangle
      using (V; W; comparison)
    frame : (diagram ∘ j) =₁ funUncurry f
    frame = Applied.W
    after-substitution : (funUncurry H ∘ s) =₁ funUncurry f
    after-substitution = Applied.V

    comparison : (frame ∙ ((diagram ◁ κ) ∙ comp-assoc s permutation diagram)) =₂
      (after-substitution ∙ (Coordinate.comparison ▷ s))
    comparison = Applied.comparison
```
