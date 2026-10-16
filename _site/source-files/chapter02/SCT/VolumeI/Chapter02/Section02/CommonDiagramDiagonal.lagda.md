# The lower diagonal image from the complete diagram beta

The lower diagonal comparison is chosen jointly with the upper one using
the original triangle matching. Its represented image follows from the
complete diagram beta and the original product-square cell. The whole
cocone pasting is specialized from the named common-axis comparison;
explicit boundary bridges retain both selected face routes. No equality
between native functor matching and a precomposition compositor is used.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.CommonDiagramDiagonal where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp-inv-left; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
  using (productMap-cong; productMap-cong₂; productMap-cong-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
  using (product-restriction; restriction-compositor; product-square)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (funEval)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
  using (evaluate-cong; evaluate⁼-absolute; evaluate⁼-composition)
open import SCT.VolumeI.Chapter01.Section08.Cocones
  using (Cocone; cocone-postcompose; square-cocone)
open import SCT.VolumeI.Chapter01.Section08.CoconeCommonAxis using (module Comparison)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle using ([2]; d₁)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.SquareGluing
  using (j₀; j₁; diagonal; j₀-diagonal; j₁-diagonal; gluing-square)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations using (TrianglePresentation)
open import SCT.VolumeI.Chapter02.Section02.OriginalTriangleBoundaryComparisons using (module Boundaries)

private
  module _ {Γ : Context} where
    junction : {X C : CAT Γ} {a b c d z : MAP X C}
      (p : a =₁ b) (q : c =₁ d) (delta : b =₁ d)
      (u : b =₁ z) (v : d =₁ z) → (v ∙ delta) =₂ u
      → ((v ∙ q) ∙ (q ⁻¹ ∙ (delta ∙ p))) =₂ (u ∙ p)
    junction p q delta u v law = comp₌-cong law (id₌ p) ∙
      ((comp₌-assoc v delta p) ⁻¹ ∙
        (comp₌-cong (id₌ v) (comp-inv-left q (delta ∙ p)) ∙
          comp₌-assoc v q (q ⁻¹ ∙ (delta ∙ p))))


module At {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C}
  {top : MorphismFamily x y} {right : MorphismFamily y z}
  {left : MorphismFamily x w} {bottom : MorphismFamily w z}
  {long : MorphismFamily x z}
  (given-upper : TrianglePresentation top right long)
  (given-lower : TrianglePresentation left bottom long) where
  module Selected = Boundaries given-upper given-lower
  module Upper = Selected.UpperDiagonal
  module Lower = Selected.LowerDiagonalRoute
  private
    module Diagram = Selected.Diagram
    Jd : MAP (P × [1]) (P × [2])
    Jd = product-restriction {P = P} d₁
    identity : id P =₁ id P
    identity = id₌ (id P)
    delta : (j₀ {Γ = Γ} ∘ d₁) =₁ (j₁ ∘ d₁)
    delta = j₁-diagonal {Γ = Γ} ⁻¹ ∙ j₀-diagonal {Γ = Γ}
    upper-shape : product-restriction {P = P} (j₀ ∘ d₁) =₁ product-restriction diagonal
    upper-shape = productMap-cong identity j₀-diagonal
    lower-shape : product-restriction {P = P} (j₁ ∘ d₁) =₁ product-restriction diagonal
    lower-shape = productMap-cong identity j₁-diagonal
    shape-cell : product-restriction {P = P} (j₀ ∘ d₁) =₁ product-restriction (j₁ ∘ d₁)
    shape-cell = productMap-cong identity delta
    upper-compositor : (product-restriction {P = P} j₀ ∘ Jd) =₁ product-restriction (j₀ ∘ d₁)
    upper-compositor = restriction-compositor {P = P} d₁ j₀
    lower-compositor : (product-restriction {P = P} j₁ ∘ Jd) =₁ product-restriction (j₁ ∘ d₁)
    lower-compositor = restriction-compositor {P = P} d₁ j₁

    shape-triangle : (lower-shape ∙ shape-cell) =₂ upper-shape
    shape-triangle = productMap-cong₂ (id₌ identity) (comp-inv-left j₁-diagonal j₀-diagonal) ∙
      (productMap-cong₂ (comp₌-unitˡ-One identity) (id₌ (j₁-diagonal ∙ delta)) ∙
        (productMap-cong-comp identity identity j₁-diagonal delta) ⁻¹)

    raw-square : Cocone Jd Jd (P × ([1] × [1]))
    raw-square = square-cocone (product-square {P = P} gluing-square)
    raw-matching : (product-restriction {P = P} j₀ ∘ Jd) =₁ (product-restriction j₁ ∘ Jd)
    raw-matching = Cocone.match raw-square

    axis-triangle : (Lower.axis ∙ raw-matching) =₂ Upper.axis
    axis-triangle = junction upper-compositor lower-compositor shape-cell
      upper-shape lower-shape shape-triangle

    actual = cocone-postcompose Diagram.value raw-square
    actual-matching = Cocone.match actual
    upper-associator = Upper.axis-route
    lower-associator = Lower.axis-route

    diagram-shape-triangle :
      ((Diagram.value ◁ Lower.axis) ∙ (Diagram.value ◁ raw-matching)) =₂
      (Diagram.value ◁ Upper.axis)
    diagram-shape-triangle = (postWhisker Diagram.value ◁ axis-triangle) ∙
      (postWhisker-comp₌ Diagram.value Lower.axis raw-matching) ⁻¹

    diagram-axis-triangle : (lower-associator ∙ actual-matching) =₂ upper-associator
    diagram-axis-triangle = junction
      (comp-assoc Jd (product-restriction {P = P} j₀) Diagram.value)
      (comp-assoc Jd (product-restriction {P = P} j₁) Diagram.value)
      (Diagram.value ◁ raw-matching)
      (Diagram.value ◁ Upper.axis) (Diagram.value ◁ Lower.axis) diagram-shape-triangle

    image-matching = evaluate-cong (funEval {C = [1]} {D = C}) Selected.original-matching

    module Common = Comparison Selected.full-diagram-beta
      Upper.axis-route Lower.axis-route diagram-axis-triangle Upper.source-beta
      Upper.target-beta Lower.target-beta image-matching
      (id₌ (Lower.target-beta ∙ (image-matching ∙ Upper.target-beta ⁻¹)))

    upper-boundary : Common.upper =₂ Upper.diagram-comparison
    upper-boundary = id₌ Upper.diagram-comparison

    lower-boundary : Common.lower =₂ Lower.diagram-comparison
    lower-boundary = id₌ Lower.diagram-comparison

    upper-image : evaluate-cong (funEval {C = [1]} {D = C}) Upper.comparison =₂ Common.upper
    upper-image = upper-boundary ⁻¹ ∙ Upper.image

    evaluation-composition :
      evaluate-cong (funEval {C = [1]} {D = C}) Selected.lower-diagonal =₂
      (image-matching ∙ evaluate-cong (funEval {C = [1]} {D = C}) Upper.comparison)
    evaluation-composition = comp₌-cong
        (evaluate⁼-absolute (funEval {C = [1]} {D = C}) Selected.original-matching)
        (evaluate⁼-absolute (funEval {C = [1]} {D = C}) Upper.comparison) ∙
      (evaluate⁼-composition (funEval {C = [1]} {D = C}) Selected.original-matching Upper.comparison ∙
        (evaluate⁼-absolute (funEval {C = [1]} {D = C}) Selected.lower-diagonal) ⁻¹)

  lower-image : evaluate-cong (funEval {C = [1]} {D = C}) Selected.lower-diagonal =₂
    Lower.diagram-comparison
  lower-image = lower-boundary ∙ (Common.diagonal ∙
    (comp₌-cong (id₌ image-matching) upper-image ∙ evaluation-composition))
```
