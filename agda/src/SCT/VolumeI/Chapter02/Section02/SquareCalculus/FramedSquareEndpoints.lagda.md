# From a square corner to an endpoint equation

The geometric corner comparison supplies the endpoint equation for the
corresponding horizontal arrow in the arrow category. The calculation
uses the retained double-evaluation comparison and the original side maps.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.FramedSquareEndpoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleVertices 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-boundary-normal)
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCornerEvaluation as Evaluation
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurrying as Currying
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareEndpointCalculus as Calculus
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointConeRoutes as Routes
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointFrameCones as Frames
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.InsertedShapeCorners as Shape
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates 𝒯 M ℱ using (coinsert)

module At {Γ C : CAT} (W : MAP Γ (Fun ([1] × [1]) C))
  (u v : Obj-abs [1]) {h k : MAP Γ (Ar C)} {z : MAP Γ C}
  (p : (evaluate v ∘ h) =₁ z) (q : (evaluate u ∘ k) =₁ z) where
  module Vertex = Shape.Vertex 𝒯 M ℱ u v
  module Framing = Frames.At 𝒯 M ℱ P (coinsert u) (insert v) v u
    Vertex.horizontal-frame Vertex.vertical-frame W
    using (matching; module Restricted)
  module Curried = Currying.At 𝒯 M ℱ W
  module H = Curried.Horizontal u
    using (comparison)
  module V = Curried.Vertical v
    using (boundary)
  module Route = Routes.At 𝒯 M ℱ I v u (coinsert u) (insert v) Vertex.corner W
  matching = Route.matching

  abstract
    evaluation-corner :
      ((evaluate u ◁ V.boundary) ∙ evaluate-post-at v (evaluate u) Curried.nested) =₂
      (matching ∙ (evaluate v ◁ H.comparison))
    evaluation-corner = Evaluation.At.comparison 𝒯 M ℱ P I E W u v

  module FromCone (Φ : ConeIso
    (Frames.framed-cone 𝒯 M ℱ P (funPre (coinsert u) ∘ W) (funPre (insert v) ∘ W)
      (Frames.frame 𝒯 M ℱ P (coinsert u) v Vertex.horizontal-frame W)
      (Frames.frame 𝒯 M ℱ P (insert v) u Vertex.vertical-frame W))
    (Frames.framed-cone 𝒯 M ℱ P h k p q)) where
    α = ConeIso.leftIso Φ
    β = ConeIso.rightIso Φ
    eα = evaluate v ◁ α
    eβ = evaluate u ◁ β
    η = evaluate v ◁ H.comparison
    τ = Cone.match (Framing.Restricted.target)
    b = V.boundary
    eb = evaluate u ◁ b
    tail = evaluate-post-at v (evaluate u) Curried.nested

    abstract
      corner : (p ∙ eα) =₂ (q ∙ (eβ ∙ matching))
      corner = isoComp-cong (idIso q) (isoComp-cong (idIso eβ) (Framing.matching ⁻¹)) ∙
        vertex-from-corner q p eα (eβ ∙ τ) (ConeIso.compatible Φ)

      compatible : (p ∙ (evaluate v ◁ (α ∙ H.comparison))) =₂
        (q ∙ post-boundary v (evaluate u) Curried.nested (β ∙ b))
      compatible = Calculus.At.to-endpoint 𝒯 M ℱ I Curried.nested u v
        H.comparison V.boundary matching evaluation-corner α β p q corner

  abstract
    from-endpoint : (α : (funPre (coinsert u) ∘ W) =₁ h)
      (β : (funPre (insert v) ∘ W) =₁ k) →
      (p ∙ (evaluate v ◁ (α ∙ H.comparison))) =₂
        (q ∙ post-boundary v (evaluate u) Curried.nested (β ∙ V.boundary)) →
      (p ∙ (evaluate v ◁ α)) =₂
        ((q ∙ ((evaluate u ◁ β) ∙
          (Frames.frame 𝒯 M ℱ P (insert v) u Vertex.vertical-frame W) ⁻¹)) ∙
          Frames.frame 𝒯 M ℱ P (coinsert u) v Vertex.horizontal-frame W)
    from-endpoint α β endpoint =
      (isoComp-assoc-at q ((evaluate u ◁ β) ∙ Framing.Restricted.right-frame ⁻¹)
        Framing.Restricted.left-frame) ⁻¹ ∙
      isoComp-cong (idIso q)
        ((isoComp-assoc-at (evaluate u ◁ β) (Framing.Restricted.right-frame ⁻¹)
          Framing.Restricted.left-frame) ⁻¹ ∙
          isoComp-cong (idIso (evaluate u ◁ β)) Framing.matching) ∙
      Calculus.At.from-endpoint 𝒯 M ℱ I Curried.nested u v
        H.comparison V.boundary matching evaluation-corner α β p q endpoint
```
