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

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
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
module PS = Projection 𝒯

module At (Γ X C : CAT) (h : MAP Γ (Ar (Fun X C))) where
  module Coordinate = Coordinates.At 𝒯 M ℱ I Γ X C h
  open Coordinate using (H; step; fixed; permutation)

  module Endpoint (z : Obj-abs [1]) {f : MAP Γ (Fun X C)}
    (p : (H ∘ insert z) =₁ f) where
    module Insert = Insertion.At.Endpoint 𝒯 M ℱ I Γ X z
    module Product = Substitution.Coordinates 𝒯 M X H (insert z)
    i = Insert.i
    j = Insert.j
    s = Insert.substitution
    κ = Insert.comparison
    χ = insert-natural (pr₁ {Γ} {X}) z
    τ = Coordinate.step-comparison
    b = pair-β₁ (i ∘ pr₁) (id X ∘ pr₂)
    associator = comp-assoc s permutation step
    before = PS.compose-base step permutation τ s b
    after = χ ⁻¹
    lifted-before = PS.lift-base H step (permutation ∘ s) before
    lifted-after = PS.lift-base H step j after
    lifted-final = PS.lift-base H pr₁ s b
    outer = comp-assoc s permutation (H ∘ step)
    output : ((H ∘ i) ∘ pr₁ {Γ} {X}) =₁ (H ∘ (i ∘ pr₁))
    output = comp-assoc pr₁ i H
    insertion : ((H ∘ i) ∘ pr₁ {Γ} {X}) =₁ ((H ∘ step) ∘ j)
    insertion = evaluate-insertion H pr₁ z
    first-frame : ((H ∘ step) ∘ j) =₁ (f ∘ pr₁ {Γ} {X})
    first-frame = (p ▷ pr₁) ∙ insertion ⁻¹
    second-frame : ((fixed ∘ pr₁) ∘ j) =₁ fixed
    second-frame = identity-boundary z fixed

    abstract
      shape : (after ∙ (step ◁ κ)) =₂ before
      shape = isoComp-assoc-at b (τ ▷ s) (associator ⁻¹) ∙
        cancel-left χ ((b ∙ (τ ▷ s)) ∙ associator ⁻¹) ∙
        isoComp-cong (idIso (χ ⁻¹)) (isoComp-assoc-at χ (b ∙ (τ ▷ s)) (associator ⁻¹)) ∙
        isoComp-cong (idIso (χ ⁻¹)) Insert.first-prescribed

      lifted-square : ((lifted-after ∙ ((H ∘ step) ◁ κ)) ∙ outer) =₂
        (lifted-final ∙ (Coordinate.first ▷ s))
      lifted-square = cancel-inverse-tail (lifted-final ∙ (Coordinate.first ▷ s)) outer ∙
        isoComp-cong ((isoComp-assoc-at lifted-final (Coordinate.first ▷ s) (outer ⁻¹)) ⁻¹) (idIso outer) ∙
        isoComp-cong ((PS.lift-compose H step permutation s τ b) ⁻¹) (idIso outer) ∙
        isoComp-cong (PS.lift-square H step before after κ shape) (idIso outer)

      inverse-insertion : insertion ⁻¹ =₂ ((output ⁻¹) ∙ lifted-after)
      inverse-insertion = isoComp-assoc-at (output ⁻¹) (H ◁ χ ⁻¹) (comp-assoc j step H) ∙
        isoComp-cong
          (isoComp-cong (idIso (output ⁻¹)) ((PS.post-inverse H χ) ⁻¹))
          (inverse-inverse (comp-assoc j step H)) ∙
        isoComp-cong (inverse-composite (H ◁ χ) output) (idIso ((comp-assoc j step H) ⁻¹ ⁻¹)) ∙
        inverse-composite ((comp-assoc j step H) ⁻¹) ((H ◁ χ) ∙ output)

      first-square :
        (first-frame ∙ (((H ∘ step) ◁ κ) ∙ outer)) =₂
        ((p ▷ pr₁) ∙ (Product.first ∙ (Coordinate.first ▷ s)))
      first-square = isoComp-cong (idIso (p ▷ pr₁))
          ((isoComp-assoc-at (output ⁻¹) lifted-final (Coordinate.first ▷ s)) ⁻¹ ∙
            isoComp-cong (idIso (output ⁻¹)) lifted-square ∙
            isoComp-cong (idIso (output ⁻¹))
              ((isoComp-assoc-at lifted-after ((H ∘ step) ◁ κ) outer) ⁻¹) ∙
            isoComp-assoc-at (output ⁻¹) lifted-after (((H ∘ step) ◁ κ) ∙ outer) ∙
            isoComp-cong inverse-insertion (idIso (((H ∘ step) ◁ κ) ∙ outer))) ∙
        isoComp-assoc-at (p ▷ pr₁) (insertion ⁻¹) (((H ∘ step) ◁ κ) ∙ outer)

      second-square :
        (second-frame ∙ (((fixed ∘ pr₁) ◁ κ) ∙ comp-assoc s permutation (fixed ∘ pr₁))) =₂
        (idIso fixed ∙ (Product.second ∙ (Coordinate.second ▷ s)))
      second-square = (isoComp-unitˡ-at (Product.second ∙ (Coordinate.second ▷ s))) ⁻¹ ∙
        cancel-inverse second-frame (Product.second ∙ (Coordinate.second ▷ s)) ∙
        isoComp-cong (idIso second-frame) Insert.second-square

    module Pair = Assembly.PairingAssembly 𝒯 M (H ∘ step) (fixed ∘ pr₁)
      permutation s j κ Coordinate.first Coordinate.second Product.first Product.second
      first-frame second-frame (p ▷ pr₁) (idIso fixed)

    paired-square : Pair.short =₂ Pair.long
    paired-square = Pair.assemble first-square second-square
```
