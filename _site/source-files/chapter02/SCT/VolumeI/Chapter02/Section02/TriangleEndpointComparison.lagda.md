# Comparing the long edge with its prescribed endpoints

A complete short-edge comparison and the two outer corner squares determine
the comparison of the long edge over its original endpoints. The pullback
recovery keeps the specified projection and matching images. Projecting the
actual three-vertex frame, then pairing its two vertex squares, compares the
literal long-edge frame with the original morphism family.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TriangleEndpointComparison where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle; unrestrict-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (CompatibleOver)
open import SCT.VolumeI.Chapter01.Section03.Products.PairedVertexFrames using (module PairedBaseImage)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle using (vertex₀; vertex₂)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (ev₀; ev₁; evAt; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.MorphismFraming using (endpoint-triangle)
open import SCT.VolumeI.Chapter02.Section01.Triangles
open import SCT.VolumeI.Chapter02.Section02.MorphismComposition using (module ComposableFamilies)
open import SCT.VolumeI.Chapter02.Section02.TriangleShortEdgeComparison using (module ShortEdgeComparison)
open import SCT.VolumeI.Chapter02.Section02.TriangleOuterFrames using (module ShortEdgeOuterFrame; module PairOuterFrame)
open import SCT.VolumeI.Chapter02.Section02.TriangleOuterFactorization using (module TriangleOuterFactorization)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module TriangleCornerFrames)
open import SCT.VolumeI.Chapter02.Section02.RecoveredVertexFrame using (module RecoveredVertexFrame)

private
  module ClearFinalAssociator {Γ : Context} {X C : CAT Γ} {a b c d e : MAP X C}
    (u : c =₁ d) (v : b =₁ c) (A : a =₁ b) (f : e =₁ d) (t : a =₁ e)
    (given : (u ∙ (v ∙ A)) =₂ (f ∙ t)) where
    comparison : (u ∙ v) =₂ (f ∙ (t ∙ A ⁻¹))
    comparison = comp₌-assoc f t (A ⁻¹) ∙
      (comp₌-cong given (id₌ (A ⁻¹)) ∙
        (comp₌-cong (comp₌-assoc u v A) (id₌ (A ⁻¹)) ∙
          (comp-inv-right (u ∙ v) A) ⁻¹))

  module AttachCorner {Γ : Context} {X C : CAT Γ} {a b c d e z : MAP X C}
    (nl : c =₁ z) (nr : d =₁ z) (L : a =₁ c) (RR : b =₁ d)
    (matching : a =₁ b) (left : a =₁ e) (right : b =₁ e)
    (junction : (right ∙ matching) =₂ left)
    (given : ((nr ⁻¹ ∙ nl) ∙ L) =₂ (RR ∙ matching)) where
    frame = (nr ∙ RR) ∙ right ⁻¹
    comparison : (nl ∙ L) =₂ (frame ∙ left)
    comparison = comp₌-cong (id₌ frame) junction ∙
      (comp₌-assoc frame right matching ∙
        (comp₌-cong ((inv-comp-right (nr ∙ RR) right) ⁻¹) (id₌ matching) ∙
          (((comp₌-assoc nr RR matching) ⁻¹) ∙
            (comp₌-cong (id₌ nr) given ∙
              (comp₌-assoc nr (nr ⁻¹ ∙ nl) L ∙
                comp₌-cong ((comp-inv-left nr nl) ⁻¹) (id₌ L))))))

module TriangleEndpointComparison {Γ : Context} {P C : CAT Γ} {f g h : MAP P C}
  (alpha : MorphismFamily f g) (beta : MorphismFamily g h) (gamma : MorphismFamily f h)
  (sigma : MAP P (Triangles C))
  (edges : ConeIdentification₁ (cone-restrict sigma (triangle-cone C))
    (ComposableFamilies.cone alpha beta))
  (long : (edge₁ ∘ sigma) =₁ MorphismFamily.arrow gamma)
  (source : (((MorphismFamily.source-frame alpha) ⁻¹ ∙ MorphismFamily.source-frame gamma) ∙
    (ev₀ ◁ long)) =₂ ((ev₀ ◁ ConeIdentification₁.left edges) ∙
      Cone.match (cone-restrict sigma (TriangleCornerFrames.source-cone C))))
  (target : (((MorphismFamily.target-frame beta) ⁻¹ ∙ MorphismFamily.target-frame gamma) ∙
    (ev₁ ◁ long)) =₂ ((ev₁ ◁ ConeIdentification₁.right edges) ∙
      Cone.match (cone-restrict sigma (TriangleCornerFrames.target-cone C)))) where
  module Short = ShortEdgeComparison alpha beta sigma edges
  module Outer = TriangleOuterFactorization alpha beta sigma Short.identification
  private
    module Input = ComposableFamilies alpha beta
    module SF = ShortEdgeOuterFrame C
    module PF = PairOuterFrame alpha beta
    module Corners = TriangleCornerFrames C
    module SC = Corners.Source sigma
    module TC = Corners.Target sigma
    q = short-edges C
    p = Input.pair-map
    delta = Short.identification
    first-beta = ConeIdentification₁.left (short-edges-image C)
    last-beta = ConeIdentification₁.right (short-edges-image C)
    input-first = ConeIdentification₁.left Input.pair-image
    input-last = ConeIdentification₁.right Input.pair-image
    left = ConeIdentification₁.left edges
    right = ConeIdentification₁.right edges
    src = ev₀ {C = C}
    tgt = ev₁ {C = C}
    s = src ∘ pullback₁ {f = tgt} {g = src}
    t = tgt ∘ pullback₂ {f = tgt} {g = src}
    v₀ = evAt {C = C} vertex₀
    v₂ = evAt {C = C} vertex₂
    outer = pair s t
    vertices = pair v₀ v₂
    ends = pair src tgt
    module First = RecoveredVertexFrame src pullback₁ q sigma p delta
      first-beta input-first left Short.left-image Corners.first-source (MorphismFamily.source-frame alpha)
    module Last = RecoveredVertexFrame tgt pullback₂ q sigma p delta
      last-beta input-last right Short.right-image Corners.second-target (MorphismFamily.target-frame beta)
    module Pair = PairedBaseImage s t q sigma p delta
      First.old-frame Last.old-frame First.new-frame Last.new-frame
      First.frame Last.frame First.compatibility Last.compatibility
    frame = pair⁼ First.frame Last.frame ∙ pair-pre v₀ v₂ sigma
    module PairSquare = ClearFinalAssociator PF.input-outer-frame (outer ◁ delta)
      (comp-assoc sigma q outer) frame (SF.short-outer-frame ▷ sigma) Pair.image
    projected-image : Outer.projected-frame =₂ frame
    projected-image = cancel-right (restrict-triangle outer q SF.short-outer-frame sigma)
      (PairSquare.comparison ∙ (Outer.outer-comparison ⁻¹))
    module Source = AttachCorner (MorphismFamily.source-frame gamma) (MorphismFamily.source-frame alpha)
      (src ◁ long) (src ◁ left) SC.matching SC.left-frame SC.right-frame SC.compatibility source
    module Target = AttachCorner (MorphismFamily.target-frame gamma) (MorphismFamily.target-frame beta)
      (tgt ◁ long) (tgt ◁ right) TC.matching TC.left-frame TC.right-frame TC.compatibility target
    source-square = unrestrict-square src edge₁ sigma (MorphismFamily.arrow gamma) long
      Corners.long-source (MorphismFamily.source-frame gamma) First.frame Source.comparison
    target-square = unrestrict-square tgt edge₁ sigma (MorphismFamily.arrow gamma) long
      Corners.long-target (MorphismFamily.target-frame gamma) Last.frame Target.comparison
    module Long = PairedBaseImage src tgt edge₁ sigma (MorphismFamily.arrow gamma) long
      Corners.long-source Corners.long-target
      (MorphismFamily.source-frame gamma) (MorphismFamily.target-frame gamma)
      First.frame Last.frame source-square target-square
    module LongSquare = ClearFinalAssociator (endpoint-triangle gamma) (ends ◁ long)
      (comp-assoc sigma edge₁ ends) frame (Outer.long-triangle ▷ sigma) Long.image

  compatible : CompatibleOver ends Outer.long-frame (endpoint-triangle gamma) long
  compatible = (Outer.long-normalization ⁻¹) ∙
    (comp₌-cong (projected-image ⁻¹) (id₌ (restrict-triangle ends edge₁ Outer.long-triangle sigma)) ∙
      LongSquare.comparison)
```
