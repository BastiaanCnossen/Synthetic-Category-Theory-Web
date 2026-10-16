# The actual outer frames of triangles and composable pairs

Both three-vertex constructions project to the paired first and last
vertex triangles. These equations retain the chosen pullback beta fields
and the literal base cells. They are computations of the existing maps,
not newly selected endpoint frames.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TriangleOuterFrames where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.TripleEvaluationOuterImage
  using (module TripleEvaluationOuterImage)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using (zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using (vertex₀; vertex₁; vertex₂; d₀; d₂; d₂-zero; d₂-one; d₀-one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (ev₀; ev₁; evAt; evAt-pre; evAt-cong; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.Triangles
open import SCT.VolumeI.Chapter02.Section02.MorphismComposition using (module ComposableFamilies)

module ShortEdgeOuterFrame {Γ : Context} (C : CAT Γ) where
  private
    q = short-edges C
    first-beta = ConeIdentification₁.left (short-edges-image C)
    last-beta = ConeIdentification₁.right (short-edges-image C)
    s = ev₀ {C = C} ∘ pullback₁ {f = ev₁ {C = C}} {g = ev₀}
    middle-projection = ev₁ {C = C} ∘ pullback₁ {f = ev₁ {C = C}} {g = ev₀}
    t = ev₁ {C = C} ∘ pullback₂ {f = ev₁ {C = C}} {g = ev₀}
    x = evAt {C = C} vertex₀
    y = evAt {C = C} vertex₁
    z = evAt {C = C} vertex₂
    first = (evAt-cong {C = C} d₂-zero ∙ evAt-pre zero d₂) ∙
      ((ev₀ ◁ first-beta) ∙ comp-assoc q pullback₁ ev₀)
    middle = (evAt-cong {C = C} d₂-one ∙ evAt-pre one d₂) ∙
      ((ev₁ ◁ first-beta) ∙ comp-assoc q pullback₁ ev₁)
    last = (evAt-cong {C = C} d₀-one ∙ evAt-pre one d₀) ∙
      ((ev₁ ◁ last-beta) ∙ comp-assoc q pullback₂ ev₁)
    module Image = TripleEvaluationOuterImage s middle-projection t q x y z first middle last

  pair-outer-frame : (outer-vertices ∘ pair-vertices C) =₁ pair s t
  pair-outer-frame = Image.before

  triangle-outer-frame : (outer-vertices ∘ triangle-vertices C) =₁ pair x z
  triangle-outer-frame = Image.after

  short-outer-frame : (pair s t ∘ q) =₁ pair x z
  short-outer-frame = pair⁼ first last ∙ pair-pre s t q

  image : (triangle-outer-frame ∙
    post-triangle outer-vertices (pair-vertices C) q
      (FunctorOverBase.cell (short-edges-over C))) =₂
    (short-outer-frame ∙ (pair-outer-frame ▷ q))
  image = Image.image

module PairOuterFrame {Γ : Context} {P C : CAT Γ} {f g h : MAP P C}
  (alpha : MorphismFamily f g) (beta : MorphismFamily g h) where
  private
    module Input = ComposableFamilies alpha beta
    q = Input.pair-map
    first-beta = ConeIdentification₁.left Input.pair-image
    last-beta = ConeIdentification₁.right Input.pair-image
    s = ev₀ {C = C} ∘ pullback₁ {f = ev₁ {C = C}} {g = ev₀}
    middle-projection = ev₁ {C = C} ∘ pullback₁ {f = ev₁ {C = C}} {g = ev₀}
    t = ev₁ {C = C} ∘ pullback₂ {f = ev₁ {C = C}} {g = ev₀}
    first = MorphismFamily.source-frame alpha ∙
      ((ev₀ ◁ first-beta) ∙ comp-assoc q pullback₁ ev₀)
    middle = MorphismFamily.target-frame alpha ∙
      ((ev₁ ◁ first-beta) ∙ comp-assoc q pullback₁ ev₁)
    last = MorphismFamily.target-frame beta ∙
      ((ev₁ ◁ last-beta) ∙ comp-assoc q pullback₂ ev₁)
    module Image = TripleEvaluationOuterImage s middle-projection t q f g h first middle last

  pair-outer-frame : (outer-vertices ∘ pair-vertices C) =₁ pair s t
  pair-outer-frame = Image.before

  input-outer-frame : (pair s t ∘ q) =₁ pair f h
  input-outer-frame = pair⁼ first last ∙ pair-pre s t q

  image : (Input.outer-frame ∙
    post-triangle outer-vertices (pair-vertices C) q
      (FunctorOverBase.cell Input.pair-over)) =₂
    (input-outer-frame ∙ (pair-outer-frame ▷ q))
  image = Image.image
```
