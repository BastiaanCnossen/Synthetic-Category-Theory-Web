# Composition computed from a prescribed triangle

A specified comparison of the short edges with a composable pair frames
the prescribed triangle over its three vertices. The relative Segal
construction then compares the chosen composite with its long edge.
A comparison of that long edge with a morphism family must retain its
complete endpoint triangle. Under that hypothesis the resulting comparison
is between the original, framed morphism families.

This is a reusable reduction for units and preservation arguments. It
constructs neither the short-edge matching nor the long-edge endpoint law.
It is an offsource candidate for the composition owner; its two small
supporting candidates must be checked before use. No new axiom is assumed.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.MorphismCompositionPresentation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc; comp₌-cong)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFraming
  using (endpoint-triangle; compare-framed-arrow)
open import SCT.VolumeI.Chapter02.Section01.Triangles
  using (Triangles; short-edges; short-edges-over; edge₁; long-edge-over; outer-vertices)
open import SCT.VolumeI.Chapter02.Section02.SegalComposition using (module ChosenComposition)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC
open import SCT.VolumeI.Chapter02.Section02.RelativeTriangleFraming using (module FrameFactorization)

module CompositionPresentation {Γ : Context} (C : CAT Γ)
  (segal : IsEquiv (short-edges C)) {P : CAT Γ} {f g h : MAP P C}
  (beta : MorphismFamily g h) (alpha : MorphismFamily f g)
  (sigma : MAP P (Triangles C))
  (short-comparison : (short-edges C ∘ sigma) =₁ MC.ComposableFamilies.pair-map alpha beta) where
  private
    module Input = MC.ComposableFamilies alpha beta
    module Composite = MC.Composition.Composite C segal beta alpha
    module Framing = FrameFactorization (short-edges-over C) Input.pair-over sigma short-comparison
    module Presented = ChosenComposition.PresentedTriangle C segal
      Framing.factor Input.pair-over Framing.comparison
    endpoints = pair (ev₀ {C = C}) ev₁

  long-endpoint-frame : (endpoints ∘ (edge₁ ∘ sigma)) =₁ pair f h
  long-endpoint-frame = Input.outer-frame ∙
    FunctorOverBase.cell (comp-over-map outer-vertices (long-edge-over C) Framing.factor)

  composite-comparison : Composite.arrow =₁ (edge₁ ∘ sigma)
  composite-comparison = IdentificationOver.identification Presented.composite

  composite-endpoint-compatible : CompatibleOver endpoints
    Composite.endpoint-frame long-endpoint-frame composite-comparison
  composite-endpoint-compatible =
    comp₌-cong (id₌ Input.outer-frame)
      (over-to-compatible (IdentificationOver.over Presented.composite)) ∙
    comp₌-assoc Input.outer-frame
      (FunctorOverBase.cell (comp-over-map outer-vertices (long-edge-over C) Framing.factor))
      (endpoints ◁ composite-comparison)

  comparison : (gamma : MorphismFamily f h)
    (long-comparison : (edge₁ ∘ sigma) =₁ MorphismFamily.arrow gamma)
    → CompatibleOver endpoints long-endpoint-frame (endpoint-triangle gamma) long-comparison
    → MorphismFamilyIdentification One (MC.Composition.compose C segal beta alpha) gamma
  comparison gamma long-comparison endpoint-compatible =
    compare-framed-arrow Composite.arrow Composite.endpoint-frame gamma
      (long-comparison ∙ composite-comparison)
      (compatible-comp endpoints Composite.endpoint-frame long-endpoint-frame
        (endpoint-triangle gamma) long-comparison composite-comparison
        endpoint-compatible composite-endpoint-compatible)
```
