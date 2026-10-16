# Forgetting the middle vertex of a prescribed triangle

The short-edge comparison frames the prescribed triangle over all three
vertices. Its projected frame satisfies the corresponding comparison of
outer vertices, with the original pullback comparisons. The endpoint
frame of its long edge is this projected frame followed by the specified
long-edge triangle. Thus the final morphism comparison reduces to the
two outer corner squares, without expanding the three-vertex frame again.

This is an offsource computation of existing witnesses. It does not
construct the short-edge comparison or the final two corner squares.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TriangleOuterFactorization where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.ProjectedFactorization
  using (module ProjectedFactorization)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using (zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using (vertex₀; vertex₂; d₁; d₁-zero; d₁-one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (ev₀; ev₁; evAt; evAt-pre; evAt-cong; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.Triangles
open import SCT.VolumeI.Chapter02.Section02.MorphismComposition using (module ComposableFamilies)
open import SCT.VolumeI.Chapter02.Section02.RelativeTriangleFraming using (module FrameFactorization)
open import SCT.VolumeI.Chapter02.Section02.TriangleOuterFrames
  using (module ShortEdgeOuterFrame; module PairOuterFrame)

module TriangleOuterFactorization {Γ : Context} {P C : CAT Γ} {f g h : MAP P C}
  (alpha : MorphismFamily f g) (beta : MorphismFamily g h)
  (sigma : MAP P (Triangles C))
  (delta : (short-edges C ∘ sigma) =₁ ComposableFamilies.pair-map alpha beta) where
  private
    module Input = ComposableFamilies alpha beta
    module Short = ShortEdgeOuterFrame C
    module Pair = PairOuterFrame alpha beta
    module Frame = FrameFactorization (short-edges-over C) Input.pair-over sigma delta
    s = ev₀ {C = C} ∘ pullback₁ {f = ev₁ {C = C}} {g = ev₀}
    t = ev₁ {C = C} ∘ pullback₂ {f = ev₁ {C = C}} {g = ev₀}
    base-outer = pair s t
    triangle-outer = pair (evAt {C = C} vertex₀) (evAt vertex₂)
    endpoints = pair (ev₀ {C = C}) ev₁
    module Projected = ProjectedFactorization
      (pair-vertices C) (triangle-vertices C) Input.vertices
      (short-edges C) sigma Input.pair-map
      (FunctorOverBase.cell (short-edges-over C)) (FunctorOverBase.cell Input.pair-over)
      delta Frame.frame (over-to-compatible (IdentificationOver.over Frame.comparison))
      outer-vertices base-outer triangle-outer (pair f h)
      Short.pair-outer-frame Short.triangle-outer-frame Input.outer-frame
      Short.short-outer-frame Pair.input-outer-frame Short.image Pair.image

  projected-frame : (triangle-outer ∘ sigma) =₁ pair f h
  projected-frame = Projected.projected-frame

  outer-comparison : (Pair.input-outer-frame ∙ (base-outer ◁ delta)) =₂
    (projected-frame ∙ restrict-triangle base-outer (short-edges C) Short.short-outer-frame sigma)
  outer-comparison = Projected.compatible

  long-triangle : (endpoints ∘ edge₁) =₁ triangle-outer
  long-triangle = pair⁼ (evAt-cong d₁-zero ∙ evAt-pre zero d₁)
    (evAt-cong d₁-one ∙ evAt-pre one d₁) ∙ pair-pre ev₀ ev₁ edge₁

  long-frame : (endpoints ∘ (edge₁ ∘ sigma)) =₁ pair f h
  long-frame = Input.outer-frame ∙
    FunctorOverBase.cell (comp-over-map outer-vertices (long-edge-over C) Frame.factor)

  private
    b = outer-vertices ◁ Frame.frame
    base-associator = comp-assoc sigma (triangle-vertices C) outer-vertices
    old = Short.triangle-outer-frame ▷ sigma
    edge = long-triangle ▷ sigma
    inverseA = (comp-assoc sigma edge₁ endpoints) ⁻¹
    cell-image : (FunctorOverBase.cell (long-edge-over C) ▷ sigma) =₂ ((old ⁻¹) ∙ edge)
    cell-image = comp₌-cong (preWhisker-inverse Short.triangle-outer-frame sigma) (id₌ edge) ∙
      preWhisker-comp₌ (Short.triangle-outer-frame ⁻¹) long-triangle sigma
    step₁ = comp₌-cong (id₌ Input.outer-frame)
      (comp₌-cong (id₌ b) (comp₌-cong (id₌ base-associator) (comp₌-cong cell-image (id₌ inverseA))))
    step₂ = comp₌-cong (id₌ Input.outer-frame)
      (comp₌-cong (id₌ b) (comp₌-cong (id₌ base-associator) (comp₌-assoc (old ⁻¹) edge inverseA)))
    step₃ = comp₌-cong (id₌ Input.outer-frame)
      (comp₌-cong (id₌ b) ((comp₌-assoc base-associator (old ⁻¹) (edge ∙ inverseA)) ⁻¹))
    step₄ = comp₌-cong (id₌ Input.outer-frame)
      ((comp₌-assoc b (base-associator ∙ (old ⁻¹)) (edge ∙ inverseA)) ⁻¹)
    step₅ = (comp₌-assoc Input.outer-frame (b ∙ (base-associator ∙ (old ⁻¹))) (edge ∙ inverseA)) ⁻¹
    coefficient = (comp₌-assoc Input.outer-frame (b ∙ base-associator) (old ⁻¹)) ⁻¹ ∙
      comp₌-cong (id₌ Input.outer-frame) ((comp₌-assoc b base-associator (old ⁻¹)) ⁻¹)
    step₆ = comp₌-cong coefficient (id₌ (edge ∙ inverseA))

  long-normalization : long-frame =₂
    (projected-frame ∙ restrict-triangle endpoints edge₁ long-triangle sigma)
  long-normalization = step₆ ∙ (step₅ ∙ (step₄ ∙ (step₃ ∙ (step₂ ∙ step₁))))
```
