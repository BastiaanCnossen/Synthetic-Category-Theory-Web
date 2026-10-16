# Recovering a triangle comparison from its short edges

A comparison with a composable family includes its middle matching square.
Pullback recovery retains both projection images and the matching image.
The chosen short-edge and composable-pair beta comparisons are used literally.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TriangleShortEdgeComparison where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (module PullbackRecovery)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (ev₀; ev₁; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.Triangles
  using (Triangles; triangle-cone; short-edges; short-edges-image)
open import SCT.VolumeI.Chapter02.Section02.MorphismComposition using (module ComposableFamilies)

module ShortEdgeComparison {Γ : Context} {P C : CAT Γ} {f g h : MAP P C}
  (alpha : MorphismFamily f g) (beta : MorphismFamily g h)
  (sigma : MAP P (Triangles C))
  (edges : ConeIdentification₁ (cone-restrict sigma (triangle-cone C))
    (ComposableFamilies.cone alpha beta)) where
  private
    module Input = ComposableFamilies alpha beta
    universal = pullback-cone (ev₁ {C = C}) ev₀

  boundary : ConeIdentification₁
    (cone-restrict (short-edges C ∘ sigma) universal)
    (cone-restrict Input.pair-map universal)
  boundary = cone-compose (cone-inverse Input.pair-image)
    (cone-compose edges
      (cone-compose (cone-identification-restrict-One sigma (short-edges-image C))
        (cone-inverse (cone-restrict-assoc sigma (short-edges C) universal))))

  module Recovery = PullbackRecovery (short-edges C ∘ sigma) Input.pair-map
    (cone-identification boundary)
  open Recovery public using (identification; recovery-law; left-image; right-image; matching-image)
```
