# Framed transport of diagram restrictions

The insertion and represented vertex calculations retain the original chosen
shape and representation comparisons. A common diagram-vertex context owns
its actual leg and vertex route; its face restrictions share those names.
A selected vertex comparison and its computation law are supplied once to
the complete edge transfer. Numbered finite pastings stay internal.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.FramedDiagramTransport where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (paste-square₌; inverse-square₌; unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp-inv-left; comp-inv-right; inv-comp-left; inv-comp-right;
    const-evaluate; const-comp; const-cong; pre-constant; preWhisker-comp₌; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-left; cancel-right; postWhisker-inverse; preWhisker-inverse; inverse-composite)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (postWhisker-id-One; whisker-mixed-One; postWhisker-comp-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (unrestrict-square; restrict-triangle; post-triangle; post-triangle-outer)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-iterated-restriction)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair-inner-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-square; pair⁼-cong; pair⁼-fixed-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
  using (product-restriction; restriction-compositor)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong; evaluate⁼-absolute)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-uncurry)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; insert; ev₀; ev₁; evAt; evAt-cong; evAt-pre; MorphismFamily; MorphismFamilyIdentification; DiagramFamily; DiagramFamilyIdentification;
    decode; encode-identification; encode-decode; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationComposition using (module InsertionComposition; module PrecompositionPointEvaluation)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters using (module PointNaturality)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationShapes using (module ShapeInsertionNaturality)


module InsertionPoints {Γ : Context} (P : CAT Γ) where
  action : {I : CAT Γ} {a b : MAP One I} → a =₁ b → insert {P = P} a =₁ insert b
  action alpha = pair⁼ (const {P = One} (id₌ (id P))) (alpha ▷ terminate P)

  action-cong : {I : CAT Γ} {a b : MAP One I} {alpha beta : a =₁ b}
    → alpha =₂ beta → action alpha =₂ action beta
  action-cong given = pair⁼-cong (id₌ (const {P = One} (id₌ (id P))))
    (preWhisker (terminate P) ◁ given)

  action-comp : {I : CAT Γ} {a b c : MAP One I} (beta : b =₁ c) (alpha : a =₁ b)
    → action (beta ∙ alpha) =₂ (action beta ∙ action alpha)
  action-comp beta alpha = pair⁼-fixed-first-comp (id P)
    (beta ▷ terminate P) (alpha ▷ terminate P) ∙
      pair⁼-cong (id₌ (const {P = One} (id₌ (id P))))
        (preWhisker-comp₌ beta alpha (terminate P))

  module Natural {I J : CAT Γ} (f : MAP I J) {a b : MAP One I} (alpha : a =₁ b) where
    private
      module Shape = InsertionComposition P
      unit = comp-unitˡ (id P)
      before = comp-assoc (terminate P) a f
      after = comp-assoc (terminate P) b f
      first-square = postWhisker-id-One (const {P = One} (id₌ (id P)))
      second-square = inverse-square₌ (whisker-mixed-One alpha (terminate P) f)

    compatibility :
      (Shape.χ f b ∙ (product-restriction {P = P} f ◁ action alpha)) =₂
      (action (f ◁ alpha) ∙ Shape.χ f a)
    compatibility = paste-square₌
      (productMap-pair-inner-One (id P) f (const {P = One} (id₌ (id P)))
        (alpha ▷ terminate P))
      (pair⁼-square first-square second-square)

module LiftedVertexSquare {Γ : Context} {I J K : CAT Γ} (P : CAT Γ)
  (d : MAP I J) (j : MAP J K) (f : MAP I K) (point : MAP One I)
  (vertex : MAP One J) (target : MAP One K)
  (theta : (j ∘ d) =₁ f) (delta : (d ∘ point) =₁ vertex)
  (nu : (j ∘ vertex) =₁ target) (kappa : (f ∘ point) =₁ target)
  (shape : (nu ∙ ((j ◁ delta) ∙ comp-assoc point d j)) =₂ (kappa ∙ (theta ▷ point))) where
  module Shape = InsertionComposition P
  module Points = InsertionPoints P
  module PointChange = Points.Natural j delta
  module ShapeChange = ShapeInsertionNaturality {P = P} theta point
  module Successive = Shape.Successive point d j
  nu-action = Points.action nu
  vertex-insertion = Shape.χ j vertex
  delta-image = Shape.J j ◁ Points.action delta
  face-image = Shape.J j ◁ Shape.χ d point
  delta-face = Shape.J j ◁ (Points.action delta ∙ Shape.χ d point)
  input-assoc = comp-assoc (insert {P = P} point) (Shape.J d) (Shape.J j)
  delta-action = Points.action (j ◁ delta)
  triangle-insertion = Shape.χ j (d ∘ point)
  shape-assoc = Points.action (comp-assoc point d j)
  shape-insertion = Shape.χ (j ∘ d) point
  compositor-at = restriction-compositor {P = P} d j ▷ insert point
  whole-before = Points.action (nu ∙ ((j ◁ delta) ∙ comp-assoc point d j))
  whole-after = Points.action (kappa ∙ (theta ▷ point))
  kappa-action = Points.action kappa
  theta-action = Points.action (theta ▷ point)
  axis-insertion = Shape.χ f point
  theta-at = productMap-cong (id₌ (id P)) theta ▷ insert point
  axis-at = (productMap-cong (id₌ (id P)) theta ∙ restriction-compositor {P = P} d j) ▷ insert point
  fold-before : (nu-action ∙ (delta-action ∙ shape-assoc)) =₂ whole-before
  fold-before = (comp₌-cong (id₌ nu-action)
    (Points.action-comp (j ◁ delta) (comp-assoc point d j)) ∙
      Points.action-comp nu ((j ◁ delta) ∙ comp-assoc point d j)) ⁻¹

  private
    step-0 : (nu-action ∙ (vertex-insertion ∙ (delta-face ∙ input-assoc))) =₂ (nu-action ∙ (vertex-insertion ∙ (delta-image ∙ (face-image ∙ input-assoc))))
    step-0 = ((comp₌-cong ((id₌ nu-action)) ((comp₌-cong ((id₌ vertex-insertion)) ((comp₌-assoc delta-image face-image input-assoc))))) ∙ (comp₌-cong ((id₌ nu-action)) ((comp₌-cong ((id₌ vertex-insertion)) ((comp₌-cong (postWhisker-comp₌ (Shape.J j) (Points.action delta) (Shape.χ d point)) ((id₌ input-assoc))))))))

  private
    step-1 : (nu-action ∙ (vertex-insertion ∙ (delta-image ∙ (face-image ∙ input-assoc)))) =₂ (nu-action ∙ (delta-action ∙ (triangle-insertion ∙ (face-image ∙ input-assoc))))
    step-1 = ((comp₌-cong ((id₌ nu-action)) ((((comp₌-cong ((id₌ delta-action)) ((comp₌-assoc triangle-insertion face-image input-assoc))) ∙ (comp₌-assoc delta-action (triangle-insertion ∙ face-image) input-assoc)) ∙ (comp₌-cong ((comp₌-assoc delta-action triangle-insertion face-image)) ((id₌ input-assoc)))))) ∙ ((comp₌-cong ((id₌ nu-action)) ((comp₌-cong ((comp₌-cong (PointChange.compatibility) ((id₌ face-image)))) ((id₌ input-assoc))))) ∙ ((comp₌-cong ((id₌ nu-action)) ((((comp₌-cong ((id₌ vertex-insertion)) ((comp₌-assoc delta-image face-image input-assoc))) ∙ (comp₌-assoc vertex-insertion (delta-image ∙ face-image) input-assoc)) ∙ (comp₌-cong ((comp₌-assoc vertex-insertion delta-image face-image)) ((id₌ input-assoc)))))) ⁻¹)))

  private
    step-2 : (nu-action ∙ (delta-action ∙ (triangle-insertion ∙ (face-image ∙ input-assoc)))) =₂ (nu-action ∙ (delta-action ∙ (shape-assoc ∙ (shape-insertion ∙ compositor-at))))
    step-2 = (comp₌-cong ((id₌ nu-action)) ((comp₌-cong ((id₌ delta-action)) (Successive.law))))

  private
    step-3 : (nu-action ∙ (delta-action ∙ (shape-assoc ∙ (shape-insertion ∙ compositor-at)))) =₂ (whole-before ∙ (shape-insertion ∙ compositor-at))
    step-3 = ((comp₌-assoc whole-before shape-insertion compositor-at) ∙ ((comp₌-cong ((comp₌-cong (fold-before) ((id₌ shape-insertion)))) ((id₌ compositor-at))) ∙ ((((comp₌-cong ((id₌ nu-action)) (((comp₌-cong ((id₌ delta-action)) ((comp₌-assoc shape-assoc shape-insertion compositor-at))) ∙ (comp₌-assoc delta-action (shape-assoc ∙ shape-insertion) compositor-at)))) ∙ (comp₌-assoc nu-action (delta-action ∙ (shape-assoc ∙ shape-insertion)) compositor-at)) ∙ (comp₌-cong (((comp₌-cong ((id₌ nu-action)) ((comp₌-assoc delta-action shape-assoc shape-insertion))) ∙ (comp₌-assoc nu-action (delta-action ∙ shape-assoc) shape-insertion))) ((id₌ compositor-at)))) ⁻¹)))

  private
    step-4 : (whole-before ∙ (shape-insertion ∙ compositor-at)) =₂ (whole-after ∙ (shape-insertion ∙ compositor-at))
    step-4 = ((comp₌-assoc whole-after shape-insertion compositor-at) ∙ ((comp₌-cong ((comp₌-cong (Points.action-cong shape) ((id₌ shape-insertion)))) ((id₌ compositor-at))) ∙ ((comp₌-assoc whole-before shape-insertion compositor-at) ⁻¹)))

  private
    step-5 : (whole-after ∙ (shape-insertion ∙ compositor-at)) =₂ (kappa-action ∙ (theta-action ∙ (shape-insertion ∙ compositor-at)))
    step-5 = ((((comp₌-cong ((id₌ kappa-action)) ((comp₌-assoc theta-action shape-insertion compositor-at))) ∙ (comp₌-assoc kappa-action (theta-action ∙ shape-insertion) compositor-at)) ∙ (comp₌-cong ((comp₌-assoc kappa-action theta-action shape-insertion)) ((id₌ compositor-at)))) ∙ ((comp₌-cong ((comp₌-cong (Points.action-comp kappa (theta ▷ point)) ((id₌ shape-insertion)))) ((id₌ compositor-at))) ∙ ((comp₌-assoc whole-after shape-insertion compositor-at) ⁻¹)))

  private
    step-6 : (kappa-action ∙ (theta-action ∙ (shape-insertion ∙ compositor-at))) =₂ (kappa-action ∙ (axis-insertion ∙ (theta-at ∙ compositor-at)))
    step-6 = ((comp₌-cong ((id₌ kappa-action)) ((comp₌-assoc axis-insertion theta-at compositor-at))) ∙ ((comp₌-cong ((id₌ kappa-action)) ((comp₌-cong ((ShapeChange.compatibility) ⁻¹) ((id₌ compositor-at))))) ∙ ((comp₌-cong ((id₌ kappa-action)) ((comp₌-assoc theta-action shape-insertion compositor-at))) ⁻¹)))

  private
    step-7 : (kappa-action ∙ (axis-insertion ∙ (theta-at ∙ compositor-at))) =₂ (kappa-action ∙ (axis-insertion ∙ axis-at))
    step-7 = (comp₌-cong ((id₌ kappa-action)) ((comp₌-cong ((id₌ axis-insertion)) ((preWhisker-comp₌ (productMap-cong (id₌ (id P)) theta) (restriction-compositor {P = P} d j) (insert point)) ⁻¹))))

  compatibility : (nu-action ∙ (vertex-insertion ∙ (delta-face ∙ input-assoc))) =₂ (kappa-action ∙ (axis-insertion ∙ axis-at))
  compatibility = step-7 ∙ step-6 ∙ step-5 ∙ step-4 ∙ step-3 ∙ step-2 ∙ step-1 ∙ step-0

module RestrictedVertexRepresentation {Γ : Context} {I K P C : CAT Γ}
  (sigma : MAP P (Fun K C)) (f : MAP I K) (point : MAP One I)
  (vertex : MAP One K) (kappa : (f ∘ point) =₁ vertex) where
  module Shape = InsertionComposition P
  module Points = InsertionPoints P
  module Point = PointNaturality sigma
  module Evaluation = PrecompositionPointEvaluation point f sigma
  diagram = funUncurry sigma
  side = funPre {D = C} f ∘ sigma
  beta = funPre-uncurry f sigma
  frame = restrict-triangle (evAt point) (funPre {D = C} f)
    (evAt-cong kappa ∙ evAt-pre point f) sigma
  u = AtPoint.uncurry-image point side
  u-inverse = u ⁻¹
  mu = AtPoint.uncurry-image vertex sigma
  mu-before = AtPoint.uncurry-image (f ∘ point) sigma
  point-change = evAt-cong {C = C} kappa ▷ sigma
  input-associator = comp-assoc sigma (funPre {D = C} f) (evAt point)
  input-frame = (evAt-pre {C = C} point f ▷ sigma) ∙ (input-associator ⁻¹)
  point-action = diagram ◁ Points.action kappa
  shape-action = diagram ◁ Shape.χ f point
  associator = comp-assoc (insert {P = P} point) (Shape.J f) diagram
  beta-at = beta ▷ insert point
  frame-expansion : frame =₂ (point-change ∙ input-frame)
  frame-expansion = comp₌-assoc point-change (evAt-pre {C = C} point f ▷ sigma)
    (input-associator ⁻¹) ∙
      comp₌-cong (preWhisker-comp₌ (evAt-cong {C = C} kappa) (evAt-pre point f) sigma)
        (id₌ (input-associator ⁻¹))

  private
    frame-step-0 : (mu ∙ (frame ∙ u-inverse)) =₂ (mu ∙ (point-change ∙ (input-frame ∙ u-inverse)))
    frame-step-0 = ((comp₌-cong ((id₌ mu)) ((comp₌-assoc point-change input-frame u-inverse))) ∙ (comp₌-cong ((id₌ mu)) ((comp₌-cong (frame-expansion) ((id₌ u-inverse))))))

  private
    frame-step-1 : (mu ∙ (point-change ∙ (input-frame ∙ u-inverse))) =₂ (point-action ∙ (mu-before ∙ (input-frame ∙ u-inverse)))
    frame-step-1 = ((((comp₌-cong ((id₌ point-action)) ((comp₌-assoc mu-before input-frame u-inverse))) ∙ (comp₌-assoc point-action (mu-before ∙ input-frame) u-inverse)) ∙ (comp₌-cong ((comp₌-assoc point-action mu-before input-frame)) ((id₌ u-inverse)))) ∙ ((comp₌-cong ((comp₌-cong (Point.uncurry-point-square kappa) ((id₌ input-frame)))) ((id₌ u-inverse))) ∙ ((((comp₌-cong ((id₌ mu)) ((comp₌-assoc point-change input-frame u-inverse))) ∙ (comp₌-assoc mu (point-change ∙ input-frame) u-inverse)) ∙ (comp₌-cong ((comp₌-assoc mu point-change input-frame)) ((id₌ u-inverse)))) ⁻¹)))

  private
    frame-step-2 : (point-action ∙ (mu-before ∙ (input-frame ∙ u-inverse))) =₂ (point-action ∙ (shape-action ∙ (associator ∙ (beta-at ∙ (u ∙ u-inverse)))))
    frame-step-2 = ((comp₌-cong ((id₌ point-action)) (((comp₌-cong ((id₌ shape-action)) (((comp₌-cong ((id₌ associator)) ((comp₌-assoc beta-at u u-inverse))) ∙ (comp₌-assoc associator (beta-at ∙ u) u-inverse)))) ∙ (comp₌-assoc shape-action (associator ∙ (beta-at ∙ u)) u-inverse)))) ∙ ((comp₌-cong ((id₌ point-action)) ((comp₌-cong (Evaluation.compatibility) ((id₌ u-inverse))))) ∙ ((comp₌-cong ((id₌ point-action)) ((comp₌-assoc mu-before input-frame u-inverse))) ⁻¹)))

  compatibility : (mu ∙ (frame ∙ u-inverse)) =₂ (point-action ∙ (shape-action ∙ (associator ∙ beta-at)))
  compatibility = comp-inv-right (point-action ∙ (shape-action ∙ (associator ∙ beta-at))) u ∙
    (((((comp₌-cong ((id₌ point-action)) (((comp₌-cong ((id₌ shape-action)) (((comp₌-cong ((id₌ associator)) ((comp₌-assoc beta-at u u-inverse))) ∙ (comp₌-assoc associator (beta-at ∙ u) u-inverse)))) ∙ (comp₌-assoc shape-action (associator ∙ (beta-at ∙ u)) u-inverse)))) ∙ (comp₌-assoc point-action (shape-action ∙ (associator ∙ (beta-at ∙ u))) u-inverse)) ∙ (comp₌-cong (((comp₌-cong ((id₌ point-action)) (((comp₌-cong ((id₌ shape-action)) ((comp₌-assoc associator beta-at u))) ∙ (comp₌-assoc shape-action (associator ∙ beta-at) u)))) ∙ (comp₌-assoc point-action (shape-action ∙ (associator ∙ beta-at)) u))) ((id₌ u-inverse)))) ⁻¹) ∙ (frame-step-2 ∙ frame-step-1 ∙ frame-step-0))

  route-action = diagram ◁ (Points.action kappa ∙ Shape.χ f point)
  route = post-triangle diagram (Shape.J f) (insert {P = P} point)
    (Points.action kappa ∙ Shape.χ f point)
  decoded-frame = frame ∙ u-inverse
  represented-route = route ∙ beta-at
  route-compatibility : (mu ∙ decoded-frame) =₂ represented-route
  route-compatibility = ((comp₌-assoc route-action associator beta-at) ⁻¹) ∙ (((comp₌-assoc route-action associator beta-at) ∙ ((comp₌-cong ((comp₌-cong ((postWhisker-comp₌ diagram (Points.action kappa) (Shape.χ f point)) ⁻¹) ((id₌ associator)))) ((id₌ beta-at))) ∙ ((((comp₌-cong ((id₌ point-action)) ((comp₌-assoc shape-action associator beta-at))) ∙ (comp₌-assoc point-action (shape-action ∙ associator) beta-at)) ∙ (comp₌-cong ((comp₌-assoc point-action shape-action associator)) ((id₌ beta-at)))) ⁻¹))) ∙ compatibility)

module DiagramVertexTransport {Γ : Context} {Y K P C : CAT Γ}
  (Jj : MAP Y K) (v : MAP P Y) (z : MAP P K)
  (vertex : (Jj ∘ v) =₁ z) (D : MAP K C) (G : MAP Y C) (leg : (D ∘ Jj) =₁ G) where
  vertex-route = post-triangle D Jj v vertex
  leg-vertex = leg ▷ v
  Zroute = leg-vertex ∙ (vertex-route ⁻¹)
  vertex-assoc = comp-assoc v Jj D

  module Restriction {X : CAT Γ} (Jd : MAP X Y) (Jf : MAP X K) (i : MAP P X)
    (axis : (Jj ∘ Jd) =₁ Jf) (input : (Jd ∘ i) =₁ v) (edge : (Jf ∘ i) =₁ z)
    (shape : (vertex ∙ ((Jj ◁ input) ∙ comp-assoc i Jd Jj)) =₂ (edge ∙ (axis ▷ i))) where
    routeF = post-triangle D Jf i edge
    routeG = post-triangle G Jd i input
    routeMiddle = post-triangle (D ∘ Jj) Jd i input
    axis-route = post-triangle D Jj Jd axis
    axis-at = axis-route ▷ i
    leg-at = (leg ▷ Jd) ▷ i
    A = comp-assoc (Jd ∘ i) Jj D
    B = comp-assoc i Jd (D ∘ Jj)
    input-action = (D ∘ Jj) ◁ input
    input-image = D ◁ (Jj ◁ input)
    output-inverse = D ◁ (vertex ⁻¹)
    solved : ((Jj ◁ input) ∙ comp-assoc i Jd Jj) =₂
      ((vertex ⁻¹) ∙ (edge ∙ (axis ▷ i)))
    solved = comp₌-cong (id₌ (vertex ⁻¹)) shape ∙
      ((inv-comp-left vertex ((Jj ◁ input) ∙ comp-assoc i Jd Jj)) ⁻¹)
    iterated : ((input-image ∙ A) ∙ B) =₂ (output-inverse ∙ (routeF ∙ axis-at))
    iterated = post-iterated-restriction D Jj Jd i axis edge (Jj ◁ input) (vertex ⁻¹) solved

    private
      inner-step-0 : (vertex-assoc ∙ (input-action ∙ B)) =₂ (input-image ∙ (A ∙ B))
      inner-step-0 = ((comp₌-assoc input-image A B) ∙ ((comp₌-cong (postWhisker-comp-One input Jj D) ((id₌ B))) ∙ ((comp₌-assoc vertex-assoc input-action B) ⁻¹)))

    private
      inner-step-1 : (input-image ∙ (A ∙ B)) =₂ (output-inverse ∙ (routeF ∙ axis-at))
      inner-step-1 = (iterated ∙ ((comp₌-assoc input-image A B) ⁻¹))

    input-image-law : (vertex-route ∙ routeMiddle) =₂ (routeF ∙ axis-at)
    input-image-law = comp-inv-left (D ◁ vertex) (routeF ∙ axis-at) ∙
      (comp₌-cong (id₌ (D ◁ vertex))
        (comp₌-cong (postWhisker-inverse D vertex) (id₌ (routeF ∙ axis-at))) ∙
          (comp₌-cong (id₌ (D ◁ vertex)) (inner-step-1 ∙ inner-step-0) ∙
            comp₌-assoc (D ◁ vertex) vertex-assoc routeMiddle))
    solved-image : (routeMiddle ∙ (axis-at ⁻¹)) =₂ ((vertex-route ⁻¹) ∙ routeF)
    solved-image = (inverse-square₌ {t = routeMiddle} {b = routeF}
      {l = axis-at} {r = vertex-route} input-image-law) ⁻¹
    leg-image : (routeG ∙ leg-at) =₂ (leg-vertex ∙ routeMiddle)
    leg-image = unconst-sides₌ (post-triangle-outer leg Jd i input)

    axis-inverse = axis-at ⁻¹
    vertex-inverse = vertex-route ⁻¹

    private
      leg-step-0 : (routeG ∙ (leg-at ∙ axis-inverse)) =₂ (leg-vertex ∙ (routeMiddle ∙ axis-inverse))
      leg-step-0 = ((comp₌-assoc leg-vertex routeMiddle axis-inverse) ∙ ((comp₌-cong (leg-image) ((id₌ axis-inverse))) ∙ ((comp₌-assoc routeG leg-at axis-inverse) ⁻¹)))

    private
      leg-step-1 : (leg-vertex ∙ (routeMiddle ∙ axis-inverse)) =₂ (leg-vertex ∙ (vertex-inverse ∙ routeF))
      leg-step-1 = (comp₌-cong ((id₌ leg-vertex)) (solved-image))

    compatibility : (routeG ∙ (leg-at ∙ axis-inverse)) =₂ (Zroute ∙ routeF)
    compatibility = ((comp₌-assoc leg-vertex vertex-inverse routeF) ⁻¹) ∙ (leg-step-1 ∙ leg-step-0)

    module Represented {H T : MAP X C}
      (betaH : H =₁ (D ∘ Jf)) (betaT : T =₁ (G ∘ Jd)) where
      raw : H =₁ T
      raw = (betaT ⁻¹) ∙ ((leg ▷ Jd) ∙ ((axis-route ⁻¹) ∙ betaH))
      expanded : H =₁ T
      expanded = (betaT ⁻¹) ∙ ((leg ▷ Jd) ∙
        ((comp-assoc Jd Jj D) ⁻¹ ∙ ((D ◁ axis) ⁻¹ ∙ betaH)))
      expanded-image : expanded =₂ raw
      expanded-image = comp₌-cong (id₌ (betaT ⁻¹))
        (comp₌-cong (id₌ (leg ▷ Jd))
          (comp₌-cong ((inverse-composite (D ◁ axis) (comp-assoc Jd Jj D)) ⁻¹)
            (id₌ betaH) ∙
              (comp₌-assoc ((comp-assoc Jd Jj D) ⁻¹) ((D ◁ axis) ⁻¹) betaH) ⁻¹))
      expanded-at = expanded ▷ i
      raw-at = raw ▷ i
      betaT-at = betaT ▷ i
      betaH-at = betaH ▷ i
      betaT-inverse-at = betaT ⁻¹ ▷ i
      betaT-inverse = betaT-at ⁻¹
      axis-inverse-at = axis-route ⁻¹ ▷ i
      tail-at = ((leg ▷ Jd) ∙ ((axis-route ⁻¹) ∙ betaH)) ▷ i
      last-at = ((axis-route ⁻¹) ∙ betaH) ▷ i

      private
        represented-step-0 : ((routeG ∙ betaT-at) ∙ expanded-at) =₂ (routeG ∙ (betaT-at ∙ raw-at))
        represented-step-0 = ((comp₌-cong ((id₌ routeG)) ((comp₌-cong ((id₌ betaT-at)) (preWhisker i ◁ expanded-image)))) ∙ (comp₌-assoc routeG betaT-at expanded-at))

      private
        represented-step-1 : (routeG ∙ (betaT-at ∙ raw-at)) =₂ (routeG ∙ (betaT-at ∙ (betaT-inverse-at ∙ tail-at)))
        represented-step-1 = (comp₌-cong ((id₌ routeG)) ((comp₌-cong ((id₌ betaT-at)) (preWhisker-comp₌ (betaT ⁻¹) ((leg ▷ Jd) ∙ ((axis-route ⁻¹) ∙ betaH)) i))))

      private
        represented-step-2 : (routeG ∙ (betaT-at ∙ (betaT-inverse-at ∙ tail-at))) =₂ (routeG ∙ (betaT-at ∙ (betaT-inverse-at ∙ (leg-at ∙ last-at))))
        represented-step-2 = (comp₌-cong ((id₌ routeG)) ((comp₌-cong ((id₌ betaT-at)) ((comp₌-cong ((id₌ betaT-inverse-at)) (preWhisker-comp₌ (leg ▷ Jd) ((axis-route ⁻¹) ∙ betaH) i))))))

      private
        represented-step-3 : (routeG ∙ (betaT-at ∙ (betaT-inverse-at ∙ (leg-at ∙ last-at)))) =₂ (routeG ∙ (betaT-at ∙ (betaT-inverse-at ∙ (leg-at ∙ (axis-inverse-at ∙ betaH-at)))))
        represented-step-3 = (comp₌-cong ((id₌ routeG)) ((comp₌-cong ((id₌ betaT-at)) ((comp₌-cong ((id₌ betaT-inverse-at)) ((comp₌-cong ((id₌ leg-at)) (preWhisker-comp₌ (axis-route ⁻¹) betaH i))))))))

      private
        represented-step-4 : (routeG ∙ (betaT-at ∙ (betaT-inverse-at ∙ (leg-at ∙ (axis-inverse-at ∙ betaH-at))))) =₂ (routeG ∙ (betaT-at ∙ (betaT-inverse ∙ (leg-at ∙ (axis-inverse-at ∙ betaH-at)))))
        represented-step-4 = ((comp₌-cong ((id₌ routeG)) ((comp₌-cong ((id₌ betaT-at)) ((((comp₌-cong ((id₌ betaT-inverse)) ((comp₌-assoc leg-at axis-inverse-at betaH-at))) ∙ (comp₌-assoc betaT-inverse (leg-at ∙ axis-inverse-at) betaH-at)) ∙ (comp₌-cong ((comp₌-assoc betaT-inverse leg-at axis-inverse-at)) ((id₌ betaH-at)))))))) ∙ ((comp₌-cong ((id₌ routeG)) ((comp₌-cong ((id₌ betaT-at)) ((comp₌-cong ((comp₌-cong ((comp₌-cong (preWhisker-inverse betaT i) ((id₌ leg-at)))) ((id₌ axis-inverse-at)))) ((id₌ betaH-at))))))) ∙ ((comp₌-cong ((id₌ routeG)) ((comp₌-cong ((id₌ betaT-at)) ((((comp₌-cong ((id₌ betaT-inverse-at)) ((comp₌-assoc leg-at axis-inverse-at betaH-at))) ∙ (comp₌-assoc betaT-inverse-at (leg-at ∙ axis-inverse-at) betaH-at)) ∙ (comp₌-cong ((comp₌-assoc betaT-inverse-at leg-at axis-inverse-at)) ((id₌ betaH-at)))))))) ⁻¹)))

      private
        represented-step-5 : (routeG ∙ (betaT-at ∙ (betaT-inverse ∙ (leg-at ∙ (axis-inverse-at ∙ betaH-at))))) =₂ (routeG ∙ (betaT-at ∙ (betaT-inverse ∙ (leg-at ∙ (axis-inverse ∙ betaH-at)))))
        represented-step-5 = (comp₌-cong ((id₌ routeG)) ((comp₌-cong ((id₌ betaT-at)) ((comp₌-cong ((id₌ betaT-inverse)) ((comp₌-cong ((id₌ leg-at)) ((comp₌-cong (preWhisker-inverse axis-route i) ((id₌ betaH-at)))))))))))

      private
        represented-step-6 : (routeG ∙ (betaT-at ∙ (betaT-inverse ∙ (leg-at ∙ (axis-inverse ∙ betaH-at))))) =₂ (routeG ∙ (leg-at ∙ (axis-inverse ∙ betaH-at)))
        represented-step-6 = (comp₌-cong ((id₌ routeG)) (comp-inv-left betaT-at (leg-at ∙ (axis-inverse ∙ betaH-at))))

      private
        represented-step-7 : (routeG ∙ (leg-at ∙ (axis-inverse ∙ betaH-at))) =₂ (Zroute ∙ (routeF ∙ betaH-at))
        represented-step-7 = ((comp₌-assoc Zroute routeF betaH-at) ∙ ((comp₌-cong (compatibility) ((id₌ betaH-at))) ∙ (((comp₌-cong ((id₌ routeG)) ((comp₌-assoc leg-at axis-inverse betaH-at))) ∙ (comp₌-assoc routeG (leg-at ∙ axis-inverse) betaH-at)) ⁻¹)))

      transfer : ((routeG ∙ betaT-at) ∙ expanded-at) =₂ (Zroute ∙ (routeF ∙ betaH-at))
      transfer = represented-step-7 ∙ represented-step-6 ∙ represented-step-5 ∙ represented-step-4 ∙ represented-step-3 ∙ represented-step-2 ∙ represented-step-1 ∙ represented-step-0

module VertexComparison {Γ : Context} {P C : CAT Γ} {s t d g : MAP P C}
  (muS : s =₁ d) (muA : t =₁ g) (Zroute : d =₁ g) where
  value : s =₁ t
  value = (muA ⁻¹) ∙ (Zroute ∙ muS)
  image : (muA ∙ value) =₂ (Zroute ∙ muS)
  image = comp-inv-left muA (Zroute ∙ muS)

module VertexTransfer {Γ : Context} {P C : CAT Γ}
  {h a s t d g : MAP P C}
  (muS : s =₁ d) (muA : t =₁ g) (qS : h =₁ s) (qA : a =₁ t)
  (edge : h =₁ a) (routeS : h =₁ d) (routeA : a =₁ g) (Zroute : d =₁ g)
  (Z : s =₁ t) (Z-image : (muA ∙ Z) =₂ (Zroute ∙ muS))
  (imageS : (muS ∙ qS) =₂ routeS) (imageA : (muA ∙ qA) =₂ routeA)
  (transport : (routeA ∙ edge) =₂ (Zroute ∙ routeS)) where
  private
    transfer-step-0 : (muA ∙ (qA ∙ edge)) =₂ (routeA ∙ edge)
    transfer-step-0 = ((comp₌-cong (imageA) ((id₌ edge))) ∙ ((comp₌-assoc muA qA edge) ⁻¹))

  private
    transfer-step-1 : (routeA ∙ edge) =₂ (Zroute ∙ routeS)
    transfer-step-1 = transport

  private
    transfer-step-2 : (Zroute ∙ routeS) =₂ (Zroute ∙ (muS ∙ qS))
    transfer-step-2 = (comp₌-cong ((id₌ Zroute)) ((imageS) ⁻¹))

  left-image : (muA ∙ (qA ∙ edge)) =₂ ((Zroute ∙ muS) ∙ qS)
  left-image = ((comp₌-assoc Zroute muS qS) ⁻¹) ∙ (transfer-step-2 ∙ transfer-step-1 ∙ transfer-step-0)
  right-image : (muA ∙ (Z ∙ qS)) =₂ ((Zroute ∙ muS) ∙ qS)
  right-image = comp₌-cong Z-image (id₌ qS) ∙
    ((comp₌-assoc muA Z qS) ⁻¹)
  compatibility : (qA ∙ edge) =₂ (Z ∙ qS)
  compatibility = cancel-left muA ((right-image ⁻¹) ∙ left-image)

module DecodedEndpointImage {Γ : Context} {P C : CAT Γ}
  (h k : MAP P (Ar C)) (point : MAP One [1]) (alpha : h =₁ k)
  {y : MAP P C} (p : (evAt point ∘ k) =₁ y) where
  uh = AtPoint.uncurry-image point h
  uk = AtPoint.uncurry-image point k
  endpoint = evAt point ◁ alpha
  diagram-endpoint = evaluate-cong (funEval {C = [1]} {D = C}) alpha ▷ insert point
  point-square : (uk ∙ endpoint) =₂ (diagram-endpoint ∙ uh)
  point-square = comp₌-cong
    (preWhisker (insert point) ◁ evaluate⁼-absolute (funEval {C = [1]} {D = C}) alpha)
    (id₌ uh) ∙ unconst-sides₌ (AtPoint.uncurry-square point alpha)
  inverted : ((uk ⁻¹) ∙ diagram-endpoint) =₂ (endpoint ∙ (uh ⁻¹))
  inverted = inverse-square₌ {t = endpoint} {b = diagram-endpoint}
    {l = uh} {r = uk} point-square
  compatibility : ((p ∙ (uk ⁻¹)) ∙ diagram-endpoint) =₂ ((p ∙ endpoint) ∙ (uh ⁻¹))
  compatibility = (comp₌-assoc p endpoint (uh ⁻¹)) ⁻¹ ∙
    (comp₌-cong (id₌ p) inverted ∙ comp₌-assoc p (uk ⁻¹) diagram-endpoint)

module _ {Γ : Context} where
  lift-edge-endpoint : {P C : CAT Γ} {h k : MAP (P × [1]) C} {y : MAP P C}
    (e : MAP One [1]) (delta : h =₁ k)
    (p : (k ∘ insert e) =₁ y) (q : (h ∘ insert e) =₁ y)
    → (p ∙ (delta ▷ insert e)) =₂ q
    → (const {P = One} p ∙ (const {P = One} delta ▷ insert e)) =₁ const q
  lift-edge-endpoint e delta p q given = const-cong given ∙
    (const-comp p (delta ▷ insert e) ∙
      comp₌-cong (id₌ (const p)) (pre-constant delta (insert e)))

```
