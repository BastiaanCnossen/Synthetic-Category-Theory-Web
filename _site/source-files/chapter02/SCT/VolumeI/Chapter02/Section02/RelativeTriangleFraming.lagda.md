# Giving a prescribed factor its relative triangle

Suppose q and p are already functors over the same base. An underlying
factor sigma of p through q, with its specified comparison delta, obtains
a triangle over the base by solving the triangle equation. The resulting
relative comparison is the original delta. This avoids making a second,
independent choice of the factor's base triangle.

For a prescribed Segal triangle this supplies the relative input to
PresentedTriangle from a complete short-edge comparison. It does not
produce that comparison, nor does it identify the long edge with any
independently framed morphism family. Those are still actual obligations.
This is an offsource candidate for a cohesive addition to OverBase or the
prescribed-triangle construction, not a proposed extra permanent file.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.RelativeTriangleFraming where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (inv-comp-right)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (IdentificationOver; identification-over; compatible-to-over)

module FrameFactorization {Γ : Context} {S : CAT Γ}
  {X Y T : CategoryOverBase S}
  (q : FunctorOverBase X Y) (p : FunctorOverBase T Y)
  (sigma : MAP (CategoryOverBase.category T) (CategoryOverBase.category X))
  (delta : (FunctorOverBase.functor q ∘ sigma) =₁ FunctorOverBase.functor p) where
  private
    base = CategoryOverBase.map Y
    image = FunctorOverBase.cell p ∙ (base ◁ delta)
    restriction = restrict-triangle base (FunctorOverBase.functor q)
      (FunctorOverBase.cell q) sigma

  frame : (CategoryOverBase.map X ∘ sigma) =₁ CategoryOverBase.map T
  frame = image ∙ restriction ⁻¹

  factor : FunctorOverBase T X
  factor = functor-over sigma frame

  comparison : IdentificationOver {A = One} (comp-over q factor) p
  comparison = identification-over delta
    (compatible-to-over ((inv-comp-right image restriction) ⁻¹))
```
