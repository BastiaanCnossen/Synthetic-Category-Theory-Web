# The two degeneracy presentations

The accepted native evaluation and corner calculations are imported as a
provider. This small consumer applies them to the six chosen shape squares
and retains complete pullback recovery for each short-edge comparison.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.UnitPresentations where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (const-One; const-pre; comp₌-assoc; comp₌-cong; inv-comp-left; comp-inv-right; inv-comp-right; comp-inv-left; preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (postWhisker-inverse; preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap; productMap-id)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
  using (product-restriction; restriction-compositor)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-β; funPre-uncurry)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
  using (evaluate-cong; evaluate⁼-absolute; evaluate-id)
open import SCT.VolumeI.Chapter01.Section07.Currying
  using (funUncurry; funCurry-β; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter01.Section08.Cocones
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; insert; identity-family; MorphismFamily; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using ([2]; d₀; d₁; d₂; s₀; s₁; s₀-d₀; s₀-d₁; s₀-d₂; s₁-d₀; s₁-d₁; s₁-d₂;
    face-middle; face-bottom; face-top)

open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-evaluate)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (evAt-cong; evAt-pre)
open import SCT.VolumeI.Chapter01.Section06.Cones using (cone-restrict)
open import SCT.VolumeI.Chapter02.Section02.UnitTriangles
  using (module UniversalEdges; module IdentityEdgePointEvaluation;
    module ConstantEdgePointEvaluation;
    source-unit-matching; target-unit-matching; source-unit-source; target-unit-source;
    source-unit-target; target-unit-target)

open import SCT.VolumeI.Chapter02.Section01.PointEvaluationCorners using (module EvaluatedVertexRoute; module RestrictedCorner)

private
  constant-boundary : {Γ : Context} (x z : MAP One ([1] {Γ = Γ}))
    → (const {P = [1]} z ∘ x) =₁ z
  constant-boundary x z = const-One z ∙ const-pre z x
```


The same corner calculation now applies to the original degeneracy shapes.
Its three uses retain the middle matching and both original outer frames.

```agda
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-right)

private
  module ShapeCorner {Γ : Context} {X C : CAT Γ}
    {a₀ a₁ b₀ b₁ l₀ r₀ z : MAP X C}
    (A : a₀ =₁ a₁) (B : b₀ =₁ b₁) (L : a₀ =₁ l₀) (RR : b₀ =₁ r₀)
    (nl : l₀ =₁ z) (nr : r₀ =₁ z) (delta : a₁ =₁ b₁)
    (compatible : ((nr ⁻¹ ∙ nl) ∙ L) =₂ (RR ∙ (B ⁻¹ ∙ (delta ∙ A)))) where
    left = nl ∙ (L ∙ A ⁻¹)
    right = nr ∙ (RR ∙ B ⁻¹)
    attach-frame : (nl ∙ L) =₂ (nr ∙ (RR ∙ (B ⁻¹ ∙ (delta ∙ A))))
    attach-frame = comp₌-cong (id₌ nr) compatible ∙
      (comp₌-assoc nr (nr ⁻¹ ∙ nl) L ∙
        comp₌-cong ((comp-inv-left nr nl) ⁻¹) (id₌ L))
    clear-left : (left ∙ A) =₂ (nl ∙ L)
    clear-left = comp₌-cong (id₌ nl) (inv-comp-right L A) ∙
      comp₌-assoc nl (L ∙ A ⁻¹) A
    expand-right : ((right ∙ delta) ∙ A) =₂ (nr ∙ (RR ∙ (B ⁻¹ ∙ (delta ∙ A))))
    expand-right = comp₌-cong (id₌ nr) (comp₌-assoc RR (B ⁻¹) (delta ∙ A)) ∙
      (comp₌-assoc nr (RR ∙ B ⁻¹) (delta ∙ A) ∙ comp₌-assoc right delta A)
    comparison : left =₂ (right ∙ delta)
    comparison = cancel-right A ((expand-right ⁻¹) ∙ (attach-frame ∙ clear-left))

  reverse-shape : {Γ : Context} {X C D : CAT Γ} {u v : MAP X C}
    (s : MAP C D) (delta : u =₁ v) {w : MAP X D}
    (L : (s ∘ u) =₁ w) (RR : (s ∘ v) =₁ w)
    → L =₂ (RR ∙ (s ◁ delta)) → RR =₂ (L ∙ (s ◁ (delta ⁻¹)))
  reverse-shape s delta L RR square =
    comp₌-cong (id₌ L) ((postWhisker-inverse s delta) ⁻¹) ∙
      ((comp-inv-right RR (s ◁ delta) ∙
        comp₌-cong square (id₌ ((s ◁ delta) ⁻¹))) ⁻¹)

module IdentityEdgeVertex {Γ : Context} (C : CAT Γ)
  (s : MAP ([2] {Γ = Γ}) [1]) (d : MAP ([1] {Γ = Γ}) [2])
  (epsilon : (s ∘ d) =₁ id [1]) (a : MAP One ([1] {Γ = Γ})) where
  module Route = EvaluatedVertexRoute {C = C} d s a epsilon (comp-unitˡ a)
  private
    module D = UniversalEdges.Degeneracy C s
    module Edge = D.IdentityEdge d epsilon
    module Point = IdentityEdgePointEvaluation C s d epsilon a
  endpoint : (comp-unitʳ (evAt {C = C} a) ∙ (evAt a ◁ Edge.comparison)) =₂
    (evAt-cong {C = C} Route.endpoint ∙ Route.route)
  endpoint = Route.normalization ∙ Point.endpoint-shape

module ConstantEdgeVertex {Γ : Context} (C : CAT Γ)
  (s : MAP ([2] {Γ = Γ}) [1]) (d : MAP ([1] {Γ = Γ}) [2])
  (z : MAP One ([1] {Γ = Γ})) (epsilon : (s ∘ d) =₁ const z) where
  module Route (a : MAP One ([1] {Γ = Γ})) =
    EvaluatedVertexRoute {C = C} d s a epsilon (const-evaluate z a)
  private
    module D = UniversalEdges.Degeneracy C s
    module Edge = D.ConstantEdge d z epsilon
    module Point = ConstantEdgePointEvaluation C s d z epsilon
    family = identity-family (evAt {C = C} z)
  source : (MorphismFamily.source-frame family ∙ (ev₀ ◁ Edge.comparison)) =₂
    (evAt-cong {C = C} (Route.endpoint zero) ∙ Route.route zero)
  source = Route.normalization zero ∙ Point.source-shape
  target : (MorphismFamily.target-frame family ∙ (ev₁ ◁ Edge.comparison)) =₂
    (evAt-cong {C = C} (Route.endpoint one) ∙ Route.route one)
  target = Route.normalization one ∙ Point.target-shape

module UnitVertices {Γ : Context} (C : CAT Γ) where
  private
    module U = UniversalEdges C
  module Source where
    private
      module Edges = U.Source
      first = identity-family (ev₀ {C = C})
      second = U.universal-arrow
      module F = MorphismFamily first
      module G = MorphismFamily second
      module H = MorphismFamily U.universal-arrow
      module FC = ConstantEdgeVertex C s₀ d₂ zero s₀-d₂
      module G₀ = IdentityEdgeVertex C s₀ d₀ s₀-d₀ zero
      module G₁ = IdentityEdgeVertex C s₀ d₀ s₀-d₀ one
      module F₀Route = FC.Route zero
      module F₁Route = FC.Route one
      module G₀Route = G₀.Route
      module G₁Route = G₁.Route
      module H₀ = IdentityEdgeVertex C s₀ d₁ s₀-d₁ zero
      module H₁ = IdentityEdgeVertex C s₀ d₁ s₀-d₁ one
      module MiddleShape = ShapeCorner {Γ = Γ} (comp-assoc one d₂ s₀) (comp-assoc zero d₀ s₀)
        (s₀-d₂ ▷ one) (s₀-d₀ ▷ zero) (constant-boundary one zero) (comp-unitˡ zero)
        (s₀ ◁ (face-middle ⁻¹)) (CoconeIdentification₁.compatible source-unit-matching)
      module SourceShape = ShapeCorner {Γ = Γ} (comp-assoc zero d₁ s₀) (comp-assoc zero d₂ s₀)
        (s₀-d₁ ▷ zero) (s₀-d₂ ▷ zero) (comp-unitˡ zero) (constant-boundary zero zero)
        (s₀ ◁ face-bottom) (CoconeIdentification₁.compatible source-unit-source)
      module TargetShape = ShapeCorner {Γ = Γ} (comp-assoc one d₀ s₀) (comp-assoc one d₁ s₀)
        (s₀-d₀ ▷ one) (s₀-d₁ ▷ one) (comp-unitˡ one) (comp-unitˡ one)
        (s₀ ◁ face-top) (CoconeIdentification₁.compatible source-unit-target)
      module Middle = RestrictedCorner {C = C} one zero d₂ d₀ s₀ (face-middle ⁻¹)
      module SourceCorner = RestrictedCorner {C = C} zero zero d₁ d₂ s₀ face-bottom
      module TargetCorner = RestrictedCorner {C = C} one one d₁ d₀ s₀ (face-top ⁻¹)

    module MiddleVertex = Middle.Framed F₁Route.endpoint G₀Route.endpoint MiddleShape.comparison
      F.target-frame G.source-frame (ev₁ ◁ Edges.First.comparison) (ev₀ ◁ Edges.Second.comparison)
      FC.target G₀.endpoint
    module SourceVertex = SourceCorner.Framed H₀.Route.endpoint F₀Route.endpoint SourceShape.comparison
      H.source-frame F.source-frame (ev₀ ◁ Edges.Long.comparison) (ev₀ ◁ Edges.First.comparison)
      H₀.endpoint FC.source
    module TargetVertex = TargetCorner.Framed H₁.Route.endpoint G₁Route.endpoint
      (reverse-shape s₀ face-top G₁Route.endpoint H₁.Route.endpoint TargetShape.comparison)
      H.target-frame G.target-frame (ev₁ ◁ Edges.Long.comparison) (ev₁ ◁ Edges.Second.comparison)
      H₁.endpoint G₁.endpoint
  module Target where
    private
      module Edges = U.Target
      first = U.universal-arrow
      second = identity-family (ev₁ {C = C})
      module F = MorphismFamily first
      module G = MorphismFamily second
      module H = MorphismFamily U.universal-arrow
      module F₀ = IdentityEdgeVertex C s₁ d₂ s₁-d₂ zero
      module F₁ = IdentityEdgeVertex C s₁ d₂ s₁-d₂ one
      module GC = ConstantEdgeVertex C s₁ d₀ one s₁-d₀
      module F₀Route = F₀.Route
      module F₁Route = F₁.Route
      module G₀Route = GC.Route zero
      module G₁Route = GC.Route one
      module H₀ = IdentityEdgeVertex C s₁ d₁ s₁-d₁ zero
      module H₁ = IdentityEdgeVertex C s₁ d₁ s₁-d₁ one
      module MiddleShape = ShapeCorner {Γ = Γ} (comp-assoc one d₂ s₁) (comp-assoc zero d₀ s₁)
        (s₁-d₂ ▷ one) (s₁-d₀ ▷ zero) (comp-unitˡ one) (constant-boundary zero one)
        (s₁ ◁ (face-middle ⁻¹)) (CoconeIdentification₁.compatible target-unit-matching)
      module SourceShape = ShapeCorner {Γ = Γ} (comp-assoc zero d₁ s₁) (comp-assoc zero d₂ s₁)
        (s₁-d₁ ▷ zero) (s₁-d₂ ▷ zero) (comp-unitˡ zero) (comp-unitˡ zero)
        (s₁ ◁ face-bottom) (CoconeIdentification₁.compatible target-unit-source)
      module TargetShape = ShapeCorner {Γ = Γ} (comp-assoc one d₀ s₁) (comp-assoc one d₁ s₁)
        (s₁-d₀ ▷ one) (s₁-d₁ ▷ one) (constant-boundary one one) (comp-unitˡ one)
        (s₁ ◁ face-top) (CoconeIdentification₁.compatible target-unit-target)
      module Middle = RestrictedCorner {C = C} one zero d₂ d₀ s₁ (face-middle ⁻¹)
      module SourceCorner = RestrictedCorner {C = C} zero zero d₁ d₂ s₁ face-bottom
      module TargetCorner = RestrictedCorner {C = C} one one d₁ d₀ s₁ (face-top ⁻¹)

    module MiddleVertex = Middle.Framed F₁Route.endpoint G₀Route.endpoint MiddleShape.comparison
      F.target-frame G.source-frame (ev₁ ◁ Edges.First.comparison) (ev₀ ◁ Edges.Second.comparison)
      F₁.endpoint GC.source
    module SourceVertex = SourceCorner.Framed H₀.Route.endpoint F₀Route.endpoint SourceShape.comparison
      H.source-frame F.source-frame (ev₀ ◁ Edges.Long.comparison) (ev₀ ◁ Edges.First.comparison)
      H₀.endpoint F₀.endpoint
    module TargetVertex = TargetCorner.Framed H₁.Route.endpoint G₁Route.endpoint
      (reverse-shape s₁ face-top G₁Route.endpoint H₁.Route.endpoint TargetShape.comparison)
      H.target-frame G.target-frame (ev₁ ◁ Edges.Long.comparison) (ev₁ ◁ Edges.Second.comparison)
      H₁.endpoint GC.target
```


The two unit degeneracies now determine whole short-edge comparisons.
Their recovery records retain the original projection and matching images.

```agda
open import SCT.VolumeI.Chapter01.Section06.Cones using (ConeIdentification₁)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (triangle-cone)
open import SCT.VolumeI.Chapter02.Section02.MorphismComposition using (module ComposableFamilies)
open import SCT.VolumeI.Chapter02.Section02.TriangleShortEdgeComparison using (module ShortEdgeComparison)

module UnitShortEdges {Γ : Context} (C : CAT Γ) where
  private
    module U = UniversalEdges C
    module Vertices = UnitVertices C
  module Source where
    first = identity-family (ev₀ {C = C})
    second = U.universal-arrow
    triangle = funPre {D = C} s₀
    private
      module Input = ComposableFamilies first second
      module Edges = U.Source
    comparison : ConeIdentification₁ (cone-restrict triangle (triangle-cone C)) Input.cone
    comparison = record
      { left = Edges.First.comparison; right = Edges.Second.comparison
      ; compatible = Vertices.Source.MiddleVertex.vertex-equation }
    module Chosen = ShortEdgeComparison first second triangle comparison
  module Target where
    first = U.universal-arrow
    second = identity-family (ev₁ {C = C})
    triangle = funPre {D = C} s₁
    private
      module Input = ComposableFamilies first second
      module Edges = U.Target
    comparison : ConeIdentification₁ (cone-restrict triangle (triangle-cone C)) Input.cone
    comparison = record
      { left = Edges.First.comparison; right = Edges.Second.comparison
      ; compatible = Vertices.Target.MiddleVertex.vertex-equation }
    module Chosen = ShortEdgeComparison first second triangle comparison
```
