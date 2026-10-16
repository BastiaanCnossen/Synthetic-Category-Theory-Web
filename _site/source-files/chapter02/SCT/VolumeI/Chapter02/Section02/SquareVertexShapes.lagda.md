# The twelve chosen face-to-vertex squares

Each square uses the original face and vertex identifications of the walking
triangle. Pairing the two endpoint computations preserves those witnesses.
The diagonal vertex frame is selected once for both triangle inclusions.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareVertexShapes where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-evaluate)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (unrestrict-square)
open import SCT.VolumeI.Chapter01.Section03.Products.PairedVertexFrames using (module PairedBaseImage)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.SquareGluing
  using (j₀; j₁; diagonal; j₀-d₀; j₀-diagonal; j₀-d₂; j₁-d₀; j₁-diagonal; j₁-d₂;
    j₀-vertex₀; j₀-vertex₁; j₀-vertex₂; j₁-vertex₀; j₁-vertex₁; j₁-vertex₂)
open import SCT.VolumeI.Chapter02.Section02.SquareCorners using (module SquareCorner)

module At {Γ : Context} where
  diagonal-vertex : (a : MAP One ([1] {Γ = Γ})) → (diagonal ∘ a) =₁ pair a a
  diagonal-vertex a = pair⁼ (comp-unitˡ a) (comp-unitˡ a) ∙ pair-pre (id [1]) (id [1]) a

  module UpperFirstSource where
    private
      module Boundary = FamilyComparison (BottomVertex.after-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₀ s₁ d₂ zero vertex₀ d₂-zero
        s₀-d₂ s₁-d₂ s₀-vertex₀ s₁-vertex₀ (const-evaluate zero zero) (comp-unitˡ zero)
        (unrestrict-square s₀ d₂ zero vertex₀ d₂-zero s₀-d₂ s₀-vertex₀
          (const-evaluate zero zero) Boundary.source)
        (unrestrict-square s₁ d₂ zero vertex₀ d₂-zero s₁-d₂ s₁-vertex₀
          (comp-unitˡ zero) Boundary.target)
    comparison :
      (j₀-vertex₀ ∙ ((j₀ ◁ d₂-zero) ∙ comp-assoc zero d₂ j₀)) =₂
      ((SquareCorner.horizontal-vertex zero zero) ∙ (j₀-d₂ ▷ zero))
    comparison = Paired.image

  module UpperFirstTarget where
    private
      module Boundary = FamilyComparison (MiddleVertex.after-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₀ s₁ d₂ one vertex₁ d₂-one
        s₀-d₂ s₁-d₂ s₀-vertex₁ s₁-vertex₁ (const-evaluate zero one) (comp-unitˡ one)
        (unrestrict-square s₀ d₂ one vertex₁ d₂-one s₀-d₂ s₀-vertex₁
          (const-evaluate zero one) Boundary.source)
        (unrestrict-square s₁ d₂ one vertex₁ d₂-one s₁-d₂ s₁-vertex₁
          (comp-unitˡ one) Boundary.target)
    comparison :
      (j₀-vertex₁ ∙ ((j₀ ◁ d₂-one) ∙ comp-assoc one d₂ j₀)) =₂
      ((SquareCorner.horizontal-vertex zero one) ∙ (j₀-d₂ ▷ one))
    comparison = Paired.image

  module UpperSecondSource where
    private
      module Boundary = FamilyComparison (MiddleVertex.before-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₀ s₁ d₀ zero vertex₁ d₀-zero
        s₀-d₀ s₁-d₀ s₀-vertex₁ s₁-vertex₁ (comp-unitˡ zero) (const-evaluate one zero)
        (unrestrict-square s₀ d₀ zero vertex₁ d₀-zero s₀-d₀ s₀-vertex₁
          (comp-unitˡ zero) Boundary.source)
        (unrestrict-square s₁ d₀ zero vertex₁ d₀-zero s₁-d₀ s₁-vertex₁
          (const-evaluate one zero) Boundary.target)
    comparison :
      (j₀-vertex₁ ∙ ((j₀ ◁ d₀-zero) ∙ comp-assoc zero d₀ j₀)) =₂
      ((SquareCorner.vertical-vertex zero one) ∙ (j₀-d₀ ▷ zero))
    comparison = Paired.image

  module UpperSecondTarget where
    private
      module Boundary = FamilyComparison (TopVertex.before-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₀ s₁ d₀ one vertex₂ d₀-one
        s₀-d₀ s₁-d₀ s₀-vertex₂ s₁-vertex₂ (comp-unitˡ one) (const-evaluate one one)
        (unrestrict-square s₀ d₀ one vertex₂ d₀-one s₀-d₀ s₀-vertex₂
          (comp-unitˡ one) Boundary.source)
        (unrestrict-square s₁ d₀ one vertex₂ d₀-one s₁-d₀ s₁-vertex₂
          (const-evaluate one one) Boundary.target)
    comparison :
      (j₀-vertex₂ ∙ ((j₀ ◁ d₀-one) ∙ comp-assoc one d₀ j₀)) =₂
      ((SquareCorner.vertical-vertex one one) ∙ (j₀-d₀ ▷ one))
    comparison = Paired.image

  module UpperDiagonalSource where
    private
      module Boundary = FamilyComparison (BottomVertex.before-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₀ s₁ d₁ zero vertex₀ d₁-zero
        s₀-d₁ s₁-d₁ s₀-vertex₀ s₁-vertex₀ (comp-unitˡ zero) (comp-unitˡ zero)
        (unrestrict-square s₀ d₁ zero vertex₀ d₁-zero s₀-d₁ s₀-vertex₀
          (comp-unitˡ zero) Boundary.source)
        (unrestrict-square s₁ d₁ zero vertex₀ d₁-zero s₁-d₁ s₁-vertex₀
          (comp-unitˡ zero) Boundary.target)
    comparison :
      (j₀-vertex₀ ∙ ((j₀ ◁ d₁-zero) ∙ comp-assoc zero d₁ j₀)) =₂
      ((diagonal-vertex zero) ∙ (j₀-diagonal ▷ zero))
    comparison = Paired.image

  module UpperDiagonalTarget where
    private
      module Boundary = FamilyComparison (TopVertex.after-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₀ s₁ d₁ one vertex₂ d₁-one
        s₀-d₁ s₁-d₁ s₀-vertex₂ s₁-vertex₂ (comp-unitˡ one) (comp-unitˡ one)
        (unrestrict-square s₀ d₁ one vertex₂ d₁-one s₀-d₁ s₀-vertex₂
          (comp-unitˡ one) Boundary.source)
        (unrestrict-square s₁ d₁ one vertex₂ d₁-one s₁-d₁ s₁-vertex₂
          (comp-unitˡ one) Boundary.target)
    comparison :
      (j₀-vertex₂ ∙ ((j₀ ◁ d₁-one) ∙ comp-assoc one d₁ j₀)) =₂
      ((diagonal-vertex one) ∙ (j₀-diagonal ▷ one))
    comparison = Paired.image

  module LowerFirstSource where
    private
      module Boundary = FamilyComparison (BottomVertex.after-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₁ s₀ d₂ zero vertex₀ d₂-zero
        s₁-d₂ s₀-d₂ s₁-vertex₀ s₀-vertex₀ (comp-unitˡ zero) (const-evaluate zero zero)
        (unrestrict-square s₁ d₂ zero vertex₀ d₂-zero s₁-d₂ s₁-vertex₀
          (comp-unitˡ zero) Boundary.target)
        (unrestrict-square s₀ d₂ zero vertex₀ d₂-zero s₀-d₂ s₀-vertex₀
          (const-evaluate zero zero) Boundary.source)
    comparison :
      (j₁-vertex₀ ∙ ((j₁ ◁ d₂-zero) ∙ comp-assoc zero d₂ j₁)) =₂
      ((SquareCorner.vertical-vertex zero zero) ∙ (j₁-d₂ ▷ zero))
    comparison = Paired.image

  module LowerFirstTarget where
    private
      module Boundary = FamilyComparison (MiddleVertex.after-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₁ s₀ d₂ one vertex₁ d₂-one
        s₁-d₂ s₀-d₂ s₁-vertex₁ s₀-vertex₁ (comp-unitˡ one) (const-evaluate zero one)
        (unrestrict-square s₁ d₂ one vertex₁ d₂-one s₁-d₂ s₁-vertex₁
          (comp-unitˡ one) Boundary.target)
        (unrestrict-square s₀ d₂ one vertex₁ d₂-one s₀-d₂ s₀-vertex₁
          (const-evaluate zero one) Boundary.source)
    comparison :
      (j₁-vertex₁ ∙ ((j₁ ◁ d₂-one) ∙ comp-assoc one d₂ j₁)) =₂
      ((SquareCorner.vertical-vertex one zero) ∙ (j₁-d₂ ▷ one))
    comparison = Paired.image

  module LowerSecondSource where
    private
      module Boundary = FamilyComparison (MiddleVertex.before-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₁ s₀ d₀ zero vertex₁ d₀-zero
        s₁-d₀ s₀-d₀ s₁-vertex₁ s₀-vertex₁ (const-evaluate one zero) (comp-unitˡ zero)
        (unrestrict-square s₁ d₀ zero vertex₁ d₀-zero s₁-d₀ s₁-vertex₁
          (const-evaluate one zero) Boundary.target)
        (unrestrict-square s₀ d₀ zero vertex₁ d₀-zero s₀-d₀ s₀-vertex₁
          (comp-unitˡ zero) Boundary.source)
    comparison :
      (j₁-vertex₁ ∙ ((j₁ ◁ d₀-zero) ∙ comp-assoc zero d₀ j₁)) =₂
      ((SquareCorner.horizontal-vertex one zero) ∙ (j₁-d₀ ▷ zero))
    comparison = Paired.image

  module LowerSecondTarget where
    private
      module Boundary = FamilyComparison (TopVertex.before-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₁ s₀ d₀ one vertex₂ d₀-one
        s₁-d₀ s₀-d₀ s₁-vertex₂ s₀-vertex₂ (const-evaluate one one) (comp-unitˡ one)
        (unrestrict-square s₁ d₀ one vertex₂ d₀-one s₁-d₀ s₁-vertex₂
          (const-evaluate one one) Boundary.target)
        (unrestrict-square s₀ d₀ one vertex₂ d₀-one s₀-d₀ s₀-vertex₂
          (comp-unitˡ one) Boundary.source)
    comparison :
      (j₁-vertex₂ ∙ ((j₁ ◁ d₀-one) ∙ comp-assoc one d₀ j₁)) =₂
      ((SquareCorner.horizontal-vertex one one) ∙ (j₁-d₀ ▷ one))
    comparison = Paired.image

  module LowerDiagonalSource where
    private
      module Boundary = FamilyComparison (BottomVertex.before-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₁ s₀ d₁ zero vertex₀ d₁-zero
        s₁-d₁ s₀-d₁ s₁-vertex₀ s₀-vertex₀ (comp-unitˡ zero) (comp-unitˡ zero)
        (unrestrict-square s₁ d₁ zero vertex₀ d₁-zero s₁-d₁ s₁-vertex₀
          (comp-unitˡ zero) Boundary.target)
        (unrestrict-square s₀ d₁ zero vertex₀ d₁-zero s₀-d₁ s₀-vertex₀
          (comp-unitˡ zero) Boundary.source)
    comparison :
      (j₁-vertex₀ ∙ ((j₁ ◁ d₁-zero) ∙ comp-assoc zero d₁ j₁)) =₂
      ((diagonal-vertex zero) ∙ (j₁-diagonal ▷ zero))
    comparison = Paired.image

  module LowerDiagonalTarget where
    private
      module Boundary = FamilyComparison (TopVertex.after-vertex {Γ = Γ})
      module Paired = PairedBaseImage s₁ s₀ d₁ one vertex₂ d₁-one
        s₁-d₁ s₀-d₁ s₁-vertex₂ s₀-vertex₂ (comp-unitˡ one) (comp-unitˡ one)
        (unrestrict-square s₁ d₁ one vertex₂ d₁-one s₁-d₁ s₁-vertex₂
          (comp-unitˡ one) Boundary.target)
        (unrestrict-square s₀ d₁ one vertex₂ d₁-one s₀-d₁ s₀-vertex₂
          (comp-unitˡ one) Boundary.source)
    comparison :
      (j₁-vertex₂ ∙ ((j₁ ◁ d₁-one) ∙ comp-assoc one d₁ j₁)) =₂
      ((diagonal-vertex one) ∙ (j₁-diagonal ▷ one))
    comparison = Paired.image
```
