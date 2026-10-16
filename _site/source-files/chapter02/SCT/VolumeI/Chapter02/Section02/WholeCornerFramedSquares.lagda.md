# Assembling a prescribed square from its four complete corners

The four inputs retain the actual native corner cones. Adjacent corners
share selected side comparisons through explicit leg computations. The
vertical family is constructed directly from the original nested square;
the two horizontal comparisons include all four endpoint clauses of the
actual framed-image constructor.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.WholeCornerFramedSquares where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; const-One)
open import SCT.VolumeI.Chapter01.Section06.Cones using (ConeIdentification₁)
open import SCT.VolumeI.Chapter01.Section06.ConeFramings using (framed-cone)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; evAt; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section02.FramedSquares
  using (FramedSquare; framed-square)
open import SCT.VolumeI.Chapter02.Section02.SquareCornerEndpoints
  using (module At; module ImageFrames)
open import SCT.VolumeI.Chapter01.Section06.FramedConePasting using (adjust)

module AtSquare {Γ : Context} {P C : CAT Γ}
  (sigma : MAP P (Fun ([1] × [1]) C)) {x y z w : MAP P C}
  (top : MorphismFamily x y) (right : MorphismFamily y z)
  (left : MorphismFamily x w) (bottom : MorphismFamily w z) where
  module Endpoint = At sigma
  module Curried = Endpoint.Curried
  private
    module T = MorphismFamily top
    module R = MorphismFamily right
    module L = MorphismFamily left
    module B = MorphismFamily bottom

  module Assemble
    (corner₀₀ : ConeIdentification₁ (Endpoint.NativeCorner.cone zero zero)
      (framed-cone ev₀ ev₀ T.arrow L.arrow T.source-frame L.source-frame))
    (corner₀₁ : ConeIdentification₁ (Endpoint.NativeCorner.cone zero one)
      (framed-cone ev₁ ev₀ T.arrow R.arrow T.target-frame R.source-frame))
    (corner₁₀ : ConeIdentification₁ (Endpoint.NativeCorner.cone one zero)
      (framed-cone ev₀ ev₁ B.arrow L.arrow B.source-frame L.target-frame))
    (corner₁₁ : ConeIdentification₁ (Endpoint.NativeCorner.cone one one)
      (framed-cone ev₁ ev₁ B.arrow R.arrow B.target-frame R.target-frame))
    (same-top : ConeIdentification₁.left corner₀₁ =₂ ConeIdentification₁.left corner₀₀)
    (same-left : ConeIdentification₁.right corner₁₀ =₂ ConeIdentification₁.right corner₀₀)
    (same-bottom : ConeIdentification₁.left corner₁₁ =₂ ConeIdentification₁.left corner₁₀)
    (same-right : ConeIdentification₁.right corner₁₁ =₂ ConeIdentification₁.right corner₀₁) where

    top-side : Curried.Horizontal.side zero =₁ T.arrow
    top-side = ConeIdentification₁.left corner₀₀
    left-side : Curried.Vertical.side zero =₁ L.arrow
    left-side = ConeIdentification₁.right corner₀₀
    bottom-side : Curried.Horizontal.side one =₁ B.arrow
    bottom-side = ConeIdentification₁.left corner₁₀
    right-side : Curried.Vertical.side one =₁ R.arrow
    right-side = ConeIdentification₁.right corner₀₁

    private
      selected₀₁ = adjust corner₀₁ top-side right-side same-top (id₌ right-side)
      selected₁₀ = adjust corner₁₀ bottom-side left-side (id₌ bottom-side) same-left
      selected₁₁ = adjust corner₁₁ bottom-side right-side same-bottom same-right

    module Corner₀₀ = Endpoint.FromCone zero zero T.arrow L.arrow
      T.source-frame L.source-frame corner₀₀
    module Corner₀₁ = Endpoint.FromCone zero one T.arrow R.arrow
      T.target-frame R.source-frame selected₀₁
    module Corner₁₀ = Endpoint.FromCone one zero B.arrow L.arrow
      B.source-frame L.target-frame selected₁₀
    module Corner₁₁ = Endpoint.FromCone one one B.arrow R.arrow
      B.target-frame R.target-frame selected₁₁

    vertical : MorphismFamily L.arrow R.arrow
    vertical = record
      { arrow = Curried.nested
      ; source-frame = Corner₀₀.vertical-boundary
      ; target-frame = Corner₀₁.vertical-boundary }

    module TopImage = ImageFrames (ev₀ {C = C}) vertical L.source-frame R.source-frame
    module BottomImage = ImageFrames (ev₁ {C = C}) vertical L.target-frame R.target-frame

    private
      frame-compatible : {f g : MAP P (Ar C)} {v : MAP P C}
        (e : MAP (Ar C) C) (p : (e ∘ g) =₁ v) (q : (e ∘ f) =₁ v)
        (delta : f =₁ g) → (p ∙ (e ◁ delta)) =₂ q
        → (const {P = One} p ∙ (e ◁ delta)) =₂ const {P = One} q
      frame-compatible e p q delta cell = (const-One q) ⁻¹ ∙
        (cell ∙ comp₌-cong (const-One p) (id₌ (e ◁ delta)))

    top-comparison : MorphismFamilyIdentification One TopImage.image top
    top-comparison = record
      { identification = Corner₀₀.horizontal-comparison
      ; source-compatible = frame-compatible ev₀ T.source-frame
          (MorphismFamily.source-frame TopImage.image) Corner₀₀.horizontal-comparison
          ((TopImage.source-normalization) ⁻¹ ∙ Corner₀₀.compatibility)
      ; target-compatible = frame-compatible ev₁ T.target-frame
          (MorphismFamily.target-frame TopImage.image) Corner₀₀.horizontal-comparison
          ((TopImage.target-normalization) ⁻¹ ∙ Corner₀₁.compatibility) }

    bottom-comparison : MorphismFamilyIdentification One BottomImage.image bottom
    bottom-comparison = record
      { identification = Corner₁₀.horizontal-comparison
      ; source-compatible = frame-compatible ev₀ B.source-frame
          (MorphismFamily.source-frame BottomImage.image) Corner₁₀.horizontal-comparison
          ((BottomImage.source-normalization) ⁻¹ ∙ Corner₁₀.compatibility)
      ; target-compatible = frame-compatible ev₁ B.target-frame
          (MorphismFamily.target-frame BottomImage.image) Corner₁₀.horizontal-comparison
          ((BottomImage.target-normalization) ⁻¹ ∙ Corner₁₁.compatibility) }

    value : FramedSquare top right left bottom
    value = framed-square vertical top-comparison bottom-comparison
```
