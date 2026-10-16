# Point evaluation transports diagram corners

The point image of a reflected edge comparison agrees with the successive
restriction route. A shape corner then transports to the corner of the
restricted diagram families, retaining the original cone matching and both
endpoint frames. One calculation serves the middle and both outer vertices
of a triangle, with arbitrary shape maps and parameter category.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PointEvaluationCorners where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
  using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; module Composition; postWhisker-id₌; preWhisker-id₌; module Boundaries; inv₌)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (const-One; const-pre; comp₌-assoc; comp₌-cong; inv-comp-left; comp-inv-right; inv-comp-right; comp-inv-left; preWhisker-comp₌; interchange-fixedInner; interchange-fixedOuter; interchange; reassociateFour; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (postWhisker-inverse; preWhisker-inverse; comp₌-unitˡ-One; comp₌-unitʳ-One; cancel-left; inverse-inverse; cancel-right)
open import SCT.VolumeI.Chapter01.Section02.Products
  using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (unconst-sides₌; paste-square₌; inverse-square₌; replace-edges₌; post-square₌; identity-square₌; pre-square₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; productMap-id)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
  using (productMap-cong; productMap-cong-triangle₁; productMap-cong-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
  using (product-restriction; restriction-compositor; module ParameterSeparation)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
  using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Functoriality
  using (funPre; funPre-β; funPre-uncurry; funPre-comp)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
  using (evaluate-cong; evaluate⁼-absolute; evaluate-id; evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Currying
  using (funUncurry; funCurry-β; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; insert; identity-family; MorphismFamily; module AtPoint; evAt-cong; evAt-pre)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (preWhisker-comp-One; postWhisker-comp-One; postWhisker-id-One; whisker-mixed-One; left-unitor-comp; right-unitor-comp; triangle-whiskered; pentagon-whiskered-right; identity-unitors)
open import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors
  using (binary-pre; binary-pre-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
  using (productMap-pair; productMap-pair-inner-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-square; pair₌-unique; pair⁼-comp; pair⁼-cong; pair⁼-id-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One; pair-pre-natural-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares
  using (pair-compatible-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
  using (RestrictionDiagram; Evaluation; restriction-diagram; evaluation)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-square-cell; post-square-cell-id; post-square-cell-comp; restrict-triangle; lies-over-comp; post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change; const-pre-iterated; post-iterated-restriction; post-triangle-comp; post-restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
  using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution
  using (module PairInput; at-pair-input-change; at-pair-restrict)
open import SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution
  using (evaluation-restriction-triangle; evaluate-restrict-inverse-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairingComposition
  using (module NormalizedComposition)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters
  using (module PointNaturality; module UncurryRoute; module ParameterInsertion; module UncurryParameter)

open import SCT.VolumeI.Chapter02.Section01.PointEvaluationComposition using (module InsertionComposition; module PrecompositionPointComposition)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters using (module RestrictionPointNaturality)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationAction using (evaluation-point-cong; evaluation-point-comp; evaluation-point-inverse)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; cone-restrict)

module EvaluatedVertexRoute {Γ : Context} {I J K C : CAT Γ}
  (d : MAP I J) (s : MAP J K) (a : MAP One I)
  {q : MAP I K} (epsilon : (s ∘ d) =₁ q)
  {z : MAP One K} (finish : (q ∘ a) =₁ z) where
  private
    F : CAT Γ
    F = Fun K C
    e : MAP (F × K) C
    e = funEval
    i : MAP F (F × I)
    i = insert a
    module Shape = InsertionComposition F
    module Native = PrecompositionPointComposition {C = C} a d s
    h = funPre {D = C} d ∘ funPre s
    restriction = productMap (id F) (s ∘ d)
    direct = post-triangle e restriction i (Shape.χ (s ∘ d) a)
    tail = (Native.diagram-image ▷ i) ∙ AtPoint.uncurry-image a h
    point-associator = comp-assoc a d s
    vertex = evAt-cong {C = C} point-associator
    output = evAt-cong {C = C} finish
    edge = evAt-cong {C = C} (epsilon ▷ a)

  endpoint : (s ∘ (d ∘ a)) =₁ z
  endpoint = finish ∙ ((epsilon ▷ a) ∙ (point-associator ⁻¹))

  route : (evAt {C = C} a ∘ h) =₁ evAt (s ∘ (d ∘ a))
  route = evAt-pre {C = C} (d ∘ a) s ∙
    ((evAt-pre {C = C} a d ▷ funPre s) ∙ (comp-assoc (funPre s) (funPre d) (evAt a)) ⁻¹)

  private
    remove-vertex : (direct ∙ tail) =₂ ((vertex ⁻¹) ∙ route)
    remove-vertex = comp₌-cong (id₌ (vertex ⁻¹)) Native.diagram-composition ∙
      ((inv-comp-left vertex (direct ∙ tail)) ⁻¹)
    endpoint-image : evAt-cong {C = C} endpoint =₂ (output ∙ (edge ∙ vertex ⁻¹))
    endpoint-image = comp₌-cong (id₌ output)
        (comp₌-cong (id₌ edge) (evaluation-point-inverse {C = C} point-associator) ∙
          evaluation-point-comp {C = C} (epsilon ▷ a) (point-associator ⁻¹)) ∙
      evaluation-point-comp {C = C} finish ((epsilon ▷ a) ∙ (point-associator ⁻¹))

  normalization : ((output ∙ edge) ∙ (direct ∙ tail)) =₂
    (evAt-cong {C = C} endpoint ∙ route)
  normalization = comp₌-cong (endpoint-image ⁻¹) (id₌ route) ∙
    (((comp₌-assoc output (edge ∙ vertex ⁻¹) route) ⁻¹) ∙
      (comp₌-cong (id₌ output) ((comp₌-assoc edge (vertex ⁻¹) route) ⁻¹) ∙
        (comp₌-cong (id₌ output) (comp₌-cong (id₌ edge) remove-vertex) ∙
          comp₌-assoc output edge (direct ∙ tail))))

module RestrictedCorner {Γ : Context} {I J K D C : CAT Γ}
  (u : MAP One I) (v : MAP One J) (d : MAP I K) (k : MAP J K)
  (s : MAP K D) (delta : (d ∘ u) =₁ (k ∘ v)) where
  private
    X : CAT Γ
    X = Fun D C
    R : MAP X (Fun K C)
    R = funPre s
    p = evAt-pre {C = C} u d
    q = evAt-pre {C = C} v k
    middle = evAt-cong {C = C} delta
    aL = comp-assoc R (funPre d) (evAt u)
    aR = comp-assoc R (funPre k) (evAt v)
    left-frame = (p ▷ R) ∙ aL ⁻¹
    right-frame = (q ▷ R) ∙ aR ⁻¹
    tau = q ⁻¹ ∙ (middle ∙ p)
    left-prefix = evAt-pre {C = C} (d ∘ u) s
    right-prefix = evAt-pre {C = C} (k ∘ v) s
    vertex = evAt-cong {C = C} (s ◁ delta)
    module Natural = RestrictionPointNaturality {C = C} s

  cone : Cone (evAt {C = C} u) (evAt v) (Fun K C)
  cone = record { left = funPre d; right = funPre k; match = tau }
  matching = Cone.match (cone-restrict R cone)
  left-route = left-prefix ∙ left-frame
  right-route = right-prefix ∙ right-frame

  private
    matching-image : (tau ▷ R) =₂ (((q ▷ R) ⁻¹) ∙ ((middle ▷ R) ∙ (p ▷ R)))
    matching-image = comp₌-cong (preWhisker-inverse q R) (preWhisker-comp₌ middle p R) ∙
      preWhisker-comp₌ (q ⁻¹) (middle ∙ p) R
    clear-frames : (right-frame ∙ matching) =₂ ((middle ▷ R) ∙ left-frame)
    clear-frames = comp₌-assoc (middle ▷ R) (p ▷ R) (aL ⁻¹) ∙
      (comp₌-cong (comp-inv-left (q ▷ R) ((middle ▷ R) ∙ (p ▷ R))) (id₌ (aL ⁻¹)) ∙
        (((comp₌-assoc (q ▷ R) (((q ▷ R) ⁻¹) ∙ ((middle ▷ R) ∙ (p ▷ R))) (aL ⁻¹)) ⁻¹) ∙
          (comp₌-cong (id₌ (q ▷ R)) (comp₌-cong matching-image (id₌ (aL ⁻¹))) ∙
            (comp₌-cong (id₌ (q ▷ R)) (inv-comp-left aR ((tau ▷ R) ∙ aL ⁻¹)) ∙
              comp₌-assoc (q ▷ R) (aR ⁻¹) matching))))

  comparison : (right-route ∙ matching) =₂ (vertex ∙ left-route)
  comparison = comp₌-assoc vertex left-prefix left-frame ∙
    (comp₌-cong (Natural.point-square delta) (id₌ left-frame) ∙
      (((comp₌-assoc right-prefix (middle ▷ R) left-frame) ⁻¹) ∙
        (comp₌-cong (id₌ right-prefix) clear-frames ∙
          comp₌-assoc right-prefix right-frame matching)))

  module Framed {z : MAP One D}
    (thetaL : (s ∘ (d ∘ u)) =₁ z) (thetaR : (s ∘ (k ∘ v)) =₁ z)
    (shape : thetaL =₂ (thetaR ∙ (s ◁ delta)))
    {a b : MAP X C} (nl : a =₁ evAt {C = C} z) (nr : b =₁ evAt z)
    (L : (evAt u ∘ (funPre d ∘ R)) =₁ a)
    (RR : (evAt v ∘ (funPre k ∘ R)) =₁ b)
    (left-image : (nl ∙ L) =₂ (evAt-cong {C = C} thetaL ∙ left-route))
    (right-image : (nr ∙ RR) =₂ (evAt-cong {C = C} thetaR ∙ right-route)) where
    private
      framed : (nl ∙ L) =₂ ((nr ∙ RR) ∙ matching)
      framed = comp₌-cong (right-image ⁻¹) (id₌ matching) ∙
        (((comp₌-assoc (evAt-cong {C = C} thetaR) right-route matching) ⁻¹) ∙
          (comp₌-cong (id₌ (evAt-cong {C = C} thetaR)) (comparison ⁻¹) ∙
            (comp₌-assoc (evAt-cong {C = C} thetaR) vertex left-route ∙
              (comp₌-cong (evaluation-point-comp {C = C} thetaR (s ◁ delta) ∙
                  evaluation-point-cong {C = C} shape) (id₌ left-route) ∙ left-image))))

    vertex-equation : ((nr ⁻¹ ∙ nl) ∙ L) =₂ (RR ∙ matching)
    vertex-equation = inv-comp-left nr (RR ∙ matching) ∙
      (comp₌-cong (id₌ (nr ⁻¹)) (comp₌-assoc nr RR matching ∙ framed) ∙
        comp₌-assoc (nr ⁻¹) nl L)
```
