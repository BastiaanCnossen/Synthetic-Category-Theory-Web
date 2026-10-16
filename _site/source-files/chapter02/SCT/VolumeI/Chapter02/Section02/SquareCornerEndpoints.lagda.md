# Complete square corners give endpoint equations

A comparison of the entire native corner cone retains both prescribed side
comparisons and their matching square. Pasting that square with the original
native double-evaluation law gives the endpoint equation for the nested
arrow. The postcomposition point and every endpoint frame stay specified.

The actual mapped and retargeted family fields have the same boundary word.
Their normalization is stated for that constructor, rather than for a newly
chosen family. This owner neither constructs the four geometric corner
comparisons nor asserts a complete glued square.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCornerEndpoints where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp-inv-left; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁)
open import SCT.VolumeI.Chapter01.Section06.ConeFramings using (framed-cone)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; evAt; ev₀; ev₁; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.PostcompositionPointNaturality
  using (module PostcompositionPointsAt)
open import SCT.VolumeI.Chapter02.Section02.SquareCurrying using (module SquareCurrying)
open import SCT.VolumeI.Chapter02.Section02.SquareCorners using (module SquareCorner)
open import SCT.VolumeI.Chapter02.Section02.SquareCornerCompatibility
  using (module SquareCornerCompatibility)
open import SCT.VolumeI.Chapter02.Section02.FramedSquares using (framed-image)

module ImageFrames {Γ : Context} {P C D : CAT Γ} (F : MAP C D)
  {f g : MAP P C} (alpha : MorphismFamily f g) {x y : MAP P D}
  (p : (F ∘ f) =₁ x) (q : (F ∘ g) =₁ y) where
  module Points = PostcompositionPointsAt F (MorphismFamily.arrow alpha)

  image : MorphismFamily x y
  image = framed-image F alpha p q

  source-boundary : (ev₀ ∘ MorphismFamily.arrow image) =₁ x
  source-boundary = p ∙
    ((F ◁ MorphismFamily.source-frame alpha) ∙ Points.point zero)

  target-boundary : (ev₁ ∘ MorphismFamily.arrow image) =₁ y
  target-boundary = q ∙
    ((F ◁ MorphismFamily.target-frame alpha) ∙ Points.point one)

  source-normalization : MorphismFamily.source-frame image =₂ source-boundary
  source-normalization = id₌ source-boundary

  target-normalization : MorphismFamily.target-frame image =₂ target-boundary
  target-normalization = id₌ target-boundary

module At {Γ : Context} {P C : CAT Γ}
  (sigma : MAP P (Fun ([1] × [1]) C)) where
  private
    I : CAT Γ
    I = [1]
  module Curried = SquareCurrying sigma

  module NativeCorner (a b : MAP One I) where
    module Horizontal = Curried.Horizontal a
    module Vertical = Curried.Vertical b
    private
      module Shape = SquareCorner a b
      module Evaluated = Shape.Evaluated C
      module Original = SquareCornerCompatibility sigma a b
      module Points = PostcompositionPointsAt (evAt {C = C} a) Curried.nested

    cone : Cone (evAt {C = C} b) (evAt a) P
    cone = Evaluated.at-family sigma

    matching : (evAt b ∘ Horizontal.side) =₁ (evAt a ∘ Vertical.side)
    matching = Cone.match cone

    horizontal-endpoint : (evAt b ∘ Horizontal.evaluated) =₁ (evAt b ∘ Horizontal.side)
    horizontal-endpoint = evAt b ◁ Horizontal.comparison

    vertical-endpoint : (evAt b ∘ Horizontal.evaluated) =₁ (evAt a ∘ Vertical.side)
    vertical-endpoint = (evAt a ◁ Vertical.boundary) ∙ Points.point b

    postcomposition-point : (evAt b ∘ Horizontal.evaluated) =₁
      (evAt a ∘ (evAt b ∘ Curried.nested))
    postcomposition-point = Points.point b

    compatibility : (matching ∙ horizontal-endpoint) =₂ vertical-endpoint
    compatibility = Original.compatibility

  module EndpointNormalization (a b : MAP One I) (h k : MAP P (Ar C)) {z : MAP P C}
    (p : (evAt b ∘ h) =₁ z) (q : (evAt a ∘ k) =₁ z)
    (left : Curried.Horizontal.side a =₁ h)
    (right : Curried.Vertical.side b =₁ k) where
    module Native = NativeCorner a b

    horizontal-comparison : Native.Horizontal.evaluated =₁ h
    horizontal-comparison = left ∙ Native.Horizontal.comparison

    vertical-boundary : (evAt b ∘ Curried.nested) =₁ k
    vertical-boundary = right ∙ Native.Vertical.boundary

    point-boundary : (evAt b ∘ Native.Horizontal.evaluated) =₁ (evAt a ∘ k)
    point-boundary = (evAt a ◁ vertical-boundary) ∙ Native.postcomposition-point

    private
      left-image = evAt b ◁ left
      right-image = evAt a ◁ right
      eta = Native.horizontal-endpoint
      boundary-image = evAt a ◁ Native.Vertical.boundary
      point = Native.postcomposition-point
      K = Native.matching

    left-normal : (p ∙ (evAt b ◁ horizontal-comparison)) =₂
      ((p ∙ left-image) ∙ eta)
    left-normal = (comp₌-assoc p left-image eta) ⁻¹ ∙
      comp₌-cong (id₌ p)
        (postWhisker-comp₌ (evAt b) left Native.Horizontal.comparison)

    right-normal : ((q ∙ (right-image ∙ K)) ∙ eta) =₂ (q ∙ point-boundary)
    right-normal = comp₌-cong (id₌ q)
        (comp₌-cong
          ((postWhisker-comp₌ (evAt a) right Native.Vertical.boundary) ⁻¹)
          (id₌ point)) ∙
      (comp₌-cong (id₌ q) ((comp₌-assoc right-image boundary-image point) ⁻¹) ∙
        (comp₌-cong (id₌ q) (comp₌-cong (id₌ right-image) Native.compatibility) ∙
          (comp₌-cong (id₌ q) (comp₌-assoc right-image K eta) ∙
            comp₌-assoc q (right-image ∙ K) eta)))


  module FromCone (a b : MAP One I) (h k : MAP P (Ar C)) {z : MAP P C}
    (p : (evAt b ∘ h) =₁ z) (q : (evAt a ∘ k) =₁ z)
    (given : ConeIdentification₁ (NativeCorner.cone a b)
      (framed-cone (evAt b) (evAt a) h k p q)) where
    module Native = NativeCorner a b

    left : Native.Horizontal.side =₁ h
    left = ConeIdentification₁.left given
    right : Native.Vertical.side =₁ k
    right = ConeIdentification₁.right given

    private
      module Normal = EndpointNormalization a b h k p q left right

    horizontal-comparison : Native.Horizontal.evaluated =₁ h
    horizontal-comparison = left ∙ Native.Horizontal.comparison

    vertical-boundary : (evAt b ∘ Curried.nested) =₁ k
    vertical-boundary = right ∙ Native.Vertical.boundary

    point-boundary : (evAt b ∘ Native.Horizontal.evaluated) =₁ (evAt a ∘ k)
    point-boundary = (evAt a ◁ vertical-boundary) ∙ Native.postcomposition-point

    private
      left-image = evAt b ◁ left
      right-image = evAt a ◁ right
      eta = Native.horizontal-endpoint
      boundary-image = evAt a ◁ Native.Vertical.boundary
      point = Native.postcomposition-point
      K = Native.matching

    corner : (p ∙ left-image) =₂ (q ∙ (right-image ∙ K))
    corner = comp₌-cong (id₌ q) (ConeIdentification₁.compatible given) ∙
      (comp₌-assoc q ((q ⁻¹) ∙ p) left-image ∙
        (comp₌-cong (comp-inv-left q p) (id₌ left-image)) ⁻¹)

    private
      left-normal : (p ∙ (evAt b ◁ horizontal-comparison)) =₂
        ((p ∙ left-image) ∙ eta)
      left-normal = Normal.left-normal

      right-normal : ((q ∙ (right-image ∙ K)) ∙ eta) =₂ (q ∙ point-boundary)
      right-normal = Normal.right-normal

    compatibility : (p ∙ (evAt b ◁ horizontal-comparison)) =₂ (q ∙ point-boundary)
    compatibility = right-normal ∙ (comp₌-cong corner (id₌ eta) ∙ left-normal)
```
