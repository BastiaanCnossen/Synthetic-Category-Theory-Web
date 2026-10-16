# Shared boundary comparisons from the complete diagram beta

The actual glued diagram and its full cocone beta select the four boundary
comparisons with the original triangles. The upper diagonal comparison is
selected from the same beta. The lower comparison is chosen jointly using
the original matching, so the prescribed diagonal comparison is shared.

This supporting draft proves that shared diagonal equation. It does not
yet prove that the chosen lower comparison has the lower diagram image.
That computation must come from the compatibility field of the full beta
before the six corner transfers can be assembled.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.OriginalTriangleBoundaryComparisons where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc; comp₌-cong; comp-inv-left)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction using (product-restriction; restriction-compositor)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-uncurry)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong)
open import SCT.VolumeI.Chapter01.Section08.Cocones using (CoconeIdentification₁)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle using ([2]; d₀; d₁; d₂)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; insert; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.SquareGluing
  using (j₀; j₁; diagonal; j₀-d₂; j₀-d₀; j₁-d₂; j₁-d₀; j₀-diagonal; j₁-diagonal; module Families)
open import SCT.VolumeI.Chapter02.Section02.SquareCoordinates using (coinsert)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations using (TrianglePresentation; module PresentedTriangle)
open import SCT.VolumeI.Chapter02.Section02.GluedTrianglePresentations using (module Glue)

module Boundaries {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C}
  {top : MorphismFamily x y} {right : MorphismFamily y z}
  {left : MorphismFamily x w} {bottom : MorphismFamily w z}
  {long : MorphismFamily x z}
  (given-upper : TrianglePresentation top right long)
  (given-lower : TrianglePresentation left bottom long) where
  module G = Glue given-upper given-lower
  module A = PresentedTriangle given-upper
  module B = PresentedTriangle given-lower
  module Diagram = Families.Diagram C G.triangles

  upper-diagram-leg = CoconeIdentification₁.left Diagram.β
  lower-diagram-leg = CoconeIdentification₁.right Diagram.β
  full-diagram-beta = Diagram.β

  module Face (j : MAP [2] ([1] × [1]))
    (triangle : MAP P (Fun [2] C))
    (leg : (Diagram.value ∘ product-restriction {P = P} j) =₁ funUncurry triangle)
    (d : MAP [1] [2]) (r : MAP [1] ([1] × [1]))
    (shape : (j ∘ d) =₁ r) where
    source : MAP P (Ar C)
    source = funPre {D = C} r ∘ G.square
    target : MAP P (Ar C)
    target = funPre {D = C} d ∘ triangle
    source-beta = funPre-uncurry r G.square
    target-beta = funPre-uncurry d triangle
    axis : (product-restriction {P = P} j ∘ product-restriction d) =₁ product-restriction r
    axis = productMap-cong (id₌ (id P)) shape ∙ restriction-compositor d j
    axis-route = post-triangle Diagram.value (product-restriction {P = P} j)
      (product-restriction d) axis

    diagram-comparison : funUncurry source =₁ funUncurry target
    diagram-comparison = target-beta ⁻¹ ∙
      ((leg ▷ product-restriction {P = P} d) ∙ (axis-route ⁻¹ ∙ source-beta))

    comparison : source =₁ target
    comparison = reflect (funEval {C = [1]} {D = C}) (funUniversal [1] C)
      source target diagram-comparison

    image : evaluate-cong (funEval {C = [1]} {D = C}) comparison =₂ diagram-comparison
    image = reflect-β-One (funEval {C = [1]} {D = C}) (funUniversal [1] C)
      source target diagram-comparison

  module Top = Face j₀ A.triangle upper-diagram-leg d₂ (coinsert zero) j₀-d₂
  module Right = Face j₀ A.triangle upper-diagram-leg d₀ (insert one) j₀-d₀
  module Left = Face j₁ B.triangle lower-diagram-leg d₂ (insert zero) j₁-d₂
  module Bottom = Face j₁ B.triangle lower-diagram-leg d₀ (coinsert one) j₁-d₀
  module UpperDiagonal = Face j₀ A.triangle upper-diagram-leg d₁ diagonal j₀-diagonal

  module LowerDiagonalRoute = Face j₁ B.triangle lower-diagram-leg d₁ diagonal j₁-diagonal

  original-matching : (funPre {D = C} d₁ ∘ A.triangle) =₁ (funPre d₁ ∘ B.triangle)
  original-matching = B.long ⁻¹ ∙ A.long

  lower-diagonal : UpperDiagonal.source =₁ (funPre {D = C} d₁ ∘ B.triangle)
  lower-diagonal = original-matching ∙ UpperDiagonal.comparison

  prescribed-diagonal : UpperDiagonal.source =₁ MorphismFamily.arrow long
  prescribed-diagonal = A.long ∙ UpperDiagonal.comparison

  diagonal-compatible : (B.long ∙ lower-diagonal) =₂ prescribed-diagonal
  diagonal-compatible = comp₌-cong (comp-inv-left B.long A.long)
      (id₌ UpperDiagonal.comparison) ∙
    (comp₌-assoc B.long original-matching UpperDiagonal.comparison) ⁻¹
```
