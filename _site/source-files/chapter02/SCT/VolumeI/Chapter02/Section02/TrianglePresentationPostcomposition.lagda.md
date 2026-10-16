# Postcomposition carries complete triangle presentations

A functor carries the specified triangle, its three edge comparisons and
all three corner squares to a presentation of the three image families.
The comparisons are reflected from the same uncurried diagrams; their
point equations are retained. Applying the Segal comparison in the target
therefore computes the composite of the two image families.

The final result takes a complete source triangle presentation as input.
Constructing such a presentation for the chosen source composite remains
a separate obligation for unconditional preservation of composition.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TrianglePresentationPostcomposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using (zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle using (d₀; d₁; d₂; face-middle; face-bottom; face-top)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (TrianglePresentation; triangle-presentation; presented-composition; module PresentedTriangle)
open import SCT.VolumeI.Chapter02.Section02.FramedCornerPostcomposition using (module FramedCornerImage)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

module PostPresentation {Γ : Context} {P C D : CAT Γ} (F : MAP C D)
  {f g h : MAP P C} {alpha : MorphismFamily f g} {beta : MorphismFamily g h}
  {gamma : MorphismFamily f h} (given : TrianglePresentation alpha beta gamma) where
  private
    module T = PresentedTriangle given
    module A = MorphismFamily alpha
    module B = MorphismFamily beta
    module G = MorphismFamily gamma
    module Middle = FramedCornerImage F one zero d₂ d₀ (face-middle ⁻¹) T.triangle
      A.arrow B.arrow A.target-frame B.source-frame T.first T.second
    module Source = FramedCornerImage F zero zero d₁ d₂ face-bottom T.triangle
      G.arrow A.arrow G.source-frame A.source-frame T.long T.first
    module Target = FramedCornerImage F one one d₁ d₀ (face-top ⁻¹) T.triangle
      G.arrow B.arrow G.target-frame B.target-frame T.long T.second
  value : TrianglePresentation (map-morphism-family F alpha)
    (map-morphism-family F beta) (map-morphism-family F gamma)
  value = triangle-presentation (funPost F ∘ T.triangle)
    Middle.first-image Middle.second-image Source.first-image
    (Middle.compatibility T.middle-compatible)
    (Source.compatibility T.source-compatible)
    (Target.compatibility T.target-compatible)

  composite : (segal : IsEquiv (short-edges D))
    → MorphismFamilyIdentification One
        (MC.Composition.compose D segal (map-morphism-family F beta) (map-morphism-family F alpha))
        (map-morphism-family F gamma)
  composite segal = presented-composition segal
    (map-morphism-family F alpha) (map-morphism-family F beta) (map-morphism-family F gamma) value
```
