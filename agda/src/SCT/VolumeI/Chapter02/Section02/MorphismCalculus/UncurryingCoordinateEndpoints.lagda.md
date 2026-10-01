# Endpoint equations for the exchanged evaluation diagram

The insertion witness has prescribed images in the two evaluation
coordinates. Postcomposition transports the first image through the
diagram, while the second is already the required constant-coordinate
equation. Pairing assembles these equations with their specified frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingCoordinateEndpoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingInsertion as Insertion
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionCoordinates as Coordinates
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as Substitution
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity as Assembly
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projection
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionEvaluation 𝒯 M ℱ
  using (evaluate-insertion)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open Assembly 𝒯 M using (cancel-inverse-tail)
open Projection 𝒯 using (compose-base; lift-base; lift-compose; lift-square; post-inverse)

-- Restructured: results of other modules are used through private
-- abbreviations with explicit arguments instead of module instantiations.
-- Only the names used downstream (through EvaluatedUncurryingEndpoints) are
-- exported from At.Endpoint.
module At (Γ X C : CAT) (h : MAP Γ (Ar (Fun X C))) where
  private
    H = Coordinates.At.H 𝒯 M ℱ I Γ X C h
    step = Coordinates.At.step 𝒯 M ℱ I Γ X C h
    fixed = Coordinates.At.fixed 𝒯 M ℱ I Γ X C h
    permutation = Coordinates.At.permutation 𝒯 M ℱ I Γ X C h
    first-coordinate = Coordinates.At.first 𝒯 M ℱ I Γ X C h
    second-coordinate = Coordinates.At.second 𝒯 M ℱ I Γ X C h
    τ = Coordinates.At.step-comparison 𝒯 M ℱ I Γ X C h

  module Endpoint (z : Obj-abs [1]) {f : MAP Γ (Fun X C)}
    (p : (H ∘ insert z) =₁ f) where
    i = Insertion.At.Endpoint.i 𝒯 M ℱ I Γ X z
    j = Insertion.At.Endpoint.j 𝒯 M ℱ I Γ X z
    s = Insertion.At.Endpoint.substitution 𝒯 M ℱ I Γ X z
    κ = Insertion.At.Endpoint.comparison 𝒯 M ℱ I Γ X z
    private
      first-prescribed = Insertion.At.Endpoint.first-prescribed 𝒯 M ℱ I Γ X z
      second-prescribed = Insertion.At.Endpoint.second-square 𝒯 M ℱ I Γ X z
      product-first = Substitution.Coordinates.first 𝒯 M X H (insert z)
      product-second = Substitution.Coordinates.second 𝒯 M X H (insert z)
      χ = insert-natural (pr₁ {Γ} {X}) z
      b = pair-β₁ (i ∘ pr₁) (id X ∘ pr₂)
      associator = comp-assoc s permutation step
      before = compose-base step permutation τ s b
      after = χ ⁻¹
      lifted-before = lift-base H step (permutation ∘ s) before
      lifted-after = lift-base H step j after
      lifted-final = lift-base H pr₁ s b
      outer = comp-assoc s permutation (H ∘ step)
      output : ((H ∘ i) ∘ pr₁ {Γ} {X}) =₁ (H ∘ (i ∘ pr₁))
      output = comp-assoc pr₁ i H
      insertion : ((H ∘ i) ∘ pr₁ {Γ} {X}) =₁ ((H ∘ step) ∘ j)
      insertion = evaluate-insertion H pr₁ z
    first-frame : ((H ∘ step) ∘ j) =₁ (f ∘ pr₁ {Γ} {X})
    first-frame = (p ▷ pr₁) ∙ insertion ⁻¹
    second-frame : ((fixed ∘ pr₁) ∘ j) =₁ fixed
    second-frame = identity-boundary z fixed

    private
      abstract
        shape : (after ∙ (step ◁ κ)) =₂ before
        shape = isoComp-assoc-at b (τ ▷ s) (associator ⁻¹) ∙
          cancel-left χ ((b ∙ (τ ▷ s)) ∙ associator ⁻¹) ∙
          isoComp-cong (idIso (χ ⁻¹)) (isoComp-assoc-at χ (b ∙ (τ ▷ s)) (associator ⁻¹)) ∙
          isoComp-cong (idIso (χ ⁻¹)) first-prescribed

        lifted-square : ((lifted-after ∙ ((H ∘ step) ◁ κ)) ∙ outer) =₂
          (lifted-final ∙ (first-coordinate ▷ s))
        lifted-square = cancel-inverse-tail (lifted-final ∙ (first-coordinate ▷ s)) outer ∙
          isoComp-cong ((isoComp-assoc-at lifted-final (first-coordinate ▷ s) (outer ⁻¹)) ⁻¹) (idIso outer) ∙
          isoComp-cong ((lift-compose H step permutation s τ b) ⁻¹) (idIso outer) ∙
          isoComp-cong (lift-square H step before after κ shape) (idIso outer)

        inverse-insertion : insertion ⁻¹ =₂ ((output ⁻¹) ∙ lifted-after)
        inverse-insertion = isoComp-assoc-at (output ⁻¹) (H ◁ χ ⁻¹) (comp-assoc j step H) ∙
          isoComp-cong
            (isoComp-cong (idIso (output ⁻¹)) ((post-inverse H χ) ⁻¹))
            (inverse-inverse (comp-assoc j step H)) ∙
          isoComp-cong (inverse-composite (H ◁ χ) output) (idIso ((comp-assoc j step H) ⁻¹ ⁻¹)) ∙
          inverse-composite ((comp-assoc j step H) ⁻¹) ((H ◁ χ) ∙ output)

        first-square :
          (first-frame ∙ (((H ∘ step) ◁ κ) ∙ outer)) =₂
          ((p ▷ pr₁) ∙ (product-first ∙ (first-coordinate ▷ s)))
        first-square = isoComp-cong (idIso (p ▷ pr₁))
            ((isoComp-assoc-at (output ⁻¹) lifted-final (first-coordinate ▷ s)) ⁻¹ ∙
              isoComp-cong (idIso (output ⁻¹)) lifted-square ∙
              isoComp-cong (idIso (output ⁻¹))
                ((isoComp-assoc-at lifted-after ((H ∘ step) ◁ κ) outer) ⁻¹) ∙
              isoComp-assoc-at (output ⁻¹) lifted-after (((H ∘ step) ◁ κ) ∙ outer) ∙
              isoComp-cong inverse-insertion (idIso (((H ∘ step) ◁ κ) ∙ outer))) ∙
          isoComp-assoc-at (p ▷ pr₁) (insertion ⁻¹) (((H ∘ step) ◁ κ) ∙ outer)

        second-square :
          (second-frame ∙ (((fixed ∘ pr₁) ◁ κ) ∙ comp-assoc s permutation (fixed ∘ pr₁))) =₂
          (idIso fixed ∙ (product-second ∙ (second-coordinate ▷ s)))
        second-square = (isoComp-unitˡ-at (product-second ∙ (second-coordinate ▷ s))) ⁻¹ ∙
          cancel-inverse second-frame (product-second ∙ (second-coordinate ▷ s)) ∙
          isoComp-cong (idIso second-frame) second-prescribed

      short = Assembly.PairingAssembly.short 𝒯 M (H ∘ step) (fixed ∘ pr₁)
        permutation s j κ first-coordinate second-coordinate product-first product-second
        first-frame second-frame (p ▷ pr₁) (idIso fixed)
      long = Assembly.PairingAssembly.long 𝒯 M (H ∘ step) (fixed ∘ pr₁)
        permutation s j κ first-coordinate second-coordinate product-first product-second
        first-frame second-frame (p ▷ pr₁) (idIso fixed)

    paired-square : short =₂ long
    paired-square = Assembly.PairingAssembly.assemble 𝒯 M (H ∘ step) (fixed ∘ pr₁)
      permutation s j κ first-coordinate second-coordinate product-first product-second
      first-frame second-frame (p ▷ pr₁) (idIso fixed) first-square second-square
```
