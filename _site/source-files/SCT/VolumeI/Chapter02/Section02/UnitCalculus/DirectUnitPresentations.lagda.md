# The two unit triangles with their original endpoint frames

Each degeneracy presents the original universal arrow as a composite
with its original identity expression. The middle, source, and target
vertices are proved separately from the specified degeneracy cocones.
Segal uniqueness then gives an identification preserving both endpoints.

These are unit laws for `compose-expression` on `Ar C`. Compatibility
with the separately defined global composition and its prescribed
endpoint comparisons is a further step.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles as Direct
import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitEndpoints as EndpointsProof
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionCornerTransport as Corners
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.FramedCornerCalculus as Shapes

module SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitPresentations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.DegenerateCocones 𝒯 M ℱ P I E
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.TriangleVertices 𝒯 M ℱ P I E S
  using (module Vertices; CompositePresentation; compose-expression)

module Universal (C : CAT) where
  module U = Direct.Universal 𝒯 M ℱ P I E C
  module End = EndpointsProof.Universal 𝒯 M ℱ P I E C

  module Left where
    module D = End.Degeneracy s₀
    module F₀ = D.ConstantEdge d₂ zero s₀-d₂ zero
    module F₁ = D.ConstantEdge d₂ zero s₀-d₂ one
    module G₀ = D.IdentityEdge d₀ s₀-d₀ zero
    module G₁ = D.IdentityEdge d₀ s₀-d₀ one
    module H₀ = D.IdentityEdge d₁ s₀-d₁ zero
    module H₁ = D.IdentityEdge d₁ s₀-d₁ one
    first = identity-expression (ev₀ {C})
    second = U.arrow
    module F = MorphismExpression first
    module G = MorphismExpression second
    module H = MorphismExpression U.arrow
    module V = Vertices first second U.arrow U.Left.Triangle.triangle
      U.Left.First.comparison U.Left.Second.comparison U.Left.Long.comparison

    module MiddleShape = Shapes.At 𝒯 (comp-assoc one d₂ s₀) (comp-assoc zero d₀ s₀)
      (s₀-d₂ ▷ one) (s₀-d₀ ▷ zero) (constant-boundary one zero) (comp-unitˡ zero)
      (s₀ ◁ (face-middle ⁻¹)) (CoconeIso.compatible left-degeneracy)
    module SourceShape = Shapes.At 𝒯 (comp-assoc zero d₁ s₀) (comp-assoc zero d₂ s₀)
      (s₀-d₁ ▷ zero) (s₀-d₂ ▷ zero) (comp-unitˡ zero) (constant-boundary zero zero)
      (s₀ ◁ face-bottom) (CoconeIso.compatible left-source)
    module TargetShape = Shapes.At 𝒯 (comp-assoc one d₀ s₀) (comp-assoc one d₁ s₀)
      (s₀-d₀ ▷ one) (s₀-d₁ ▷ one) (comp-unitˡ one) (comp-unitˡ one)
      (s₀ ◁ face-top) (CoconeIso.compatible left-target)

    module Middle = Corners.At 𝒯 M ℱ P {C = C} one zero d₂ d₀ s₀ (face-middle ⁻¹)
    module Source = Corners.At 𝒯 M ℱ P {C = C} zero zero d₁ d₂ s₀ face-bottom
    module Target = Corners.At 𝒯 M ℱ P {C = C} one one d₁ d₀ s₀ (face-top ⁻¹)
    module MiddleVertex = Middle.Framed F₁.Route.endpoint G₀.Route.endpoint MiddleShape.comparison
      F.target-frame G.source-frame (ev₁ ◁ U.Left.First.comparison) (ev₀ ◁ U.Left.Second.comparison)
      F₁.endpoint G₀.endpoint
    module SourceVertex = Source.Framed H₀.Route.endpoint F₀.Route.endpoint SourceShape.comparison
      H.source-frame F.source-frame (ev₀ ◁ U.Left.Long.comparison) (ev₀ ◁ U.Left.First.comparison)
      H₀.endpoint F₀.endpoint
    module TargetVertex = Target.Framed H₁.Route.endpoint G₁.Route.endpoint
      (Shapes.reverse-shape 𝒯 s₀ face-top G₁.Route.endpoint H₁.Route.endpoint TargetShape.comparison)
      H.target-frame G.target-frame (ev₁ ◁ U.Left.Long.comparison) (ev₁ ◁ U.Left.Second.comparison)
      H₁.endpoint G₁.endpoint

    middle-vertex : V.MiddleVertex
    middle-vertex = MiddleVertex.vertex-equation

    source-vertex : V.SourceVertex
    source-vertex = SourceVertex.vertex-equation

    target-vertex : V.TargetVertex
    target-vertex = TargetVertex.vertex-equation

    presentation : CompositePresentation (identity-expression ev₀) U.arrow U.arrow
    presentation = V.presentation middle-vertex source-vertex target-vertex

    comparison : ExpressionIso (compose-expression (identity-expression ev₀) U.arrow) U.arrow
    comparison = V.composite-comparison middle-vertex source-vertex target-vertex
  module Right where
    module D = End.Degeneracy s₁
    module F₀ = D.IdentityEdge d₂ s₁-d₂ zero
    module F₁ = D.IdentityEdge d₂ s₁-d₂ one
    module G₀ = D.ConstantEdge d₀ one s₁-d₀ zero
    module G₁ = D.ConstantEdge d₀ one s₁-d₀ one
    module H₀ = D.IdentityEdge d₁ s₁-d₁ zero
    module H₁ = D.IdentityEdge d₁ s₁-d₁ one
    first = U.arrow
    second = identity-expression (ev₁ {C})
    module F = MorphismExpression first
    module G = MorphismExpression second
    module H = MorphismExpression U.arrow
    module V = Vertices first second U.arrow U.Right.Triangle.triangle
      U.Right.First.comparison U.Right.Second.comparison U.Right.Long.comparison

    module MiddleShape = Shapes.At 𝒯 (comp-assoc one d₂ s₁) (comp-assoc zero d₀ s₁)
      (s₁-d₂ ▷ one) (s₁-d₀ ▷ zero) (comp-unitˡ one) (constant-boundary zero one)
      (s₁ ◁ (face-middle ⁻¹)) (CoconeIso.compatible right-degeneracy)
    module SourceShape = Shapes.At 𝒯 (comp-assoc zero d₁ s₁) (comp-assoc zero d₂ s₁)
      (s₁-d₁ ▷ zero) (s₁-d₂ ▷ zero) (comp-unitˡ zero) (comp-unitˡ zero)
      (s₁ ◁ face-bottom) (CoconeIso.compatible right-source)
    module TargetShape = Shapes.At 𝒯 (comp-assoc one d₀ s₁) (comp-assoc one d₁ s₁)
      (s₁-d₀ ▷ one) (s₁-d₁ ▷ one) (constant-boundary one one) (comp-unitˡ one)
      (s₁ ◁ face-top) (CoconeIso.compatible right-target)

    module Middle = Corners.At 𝒯 M ℱ P {C = C} one zero d₂ d₀ s₁ (face-middle ⁻¹)
    module Source = Corners.At 𝒯 M ℱ P {C = C} zero zero d₁ d₂ s₁ face-bottom
    module Target = Corners.At 𝒯 M ℱ P {C = C} one one d₁ d₀ s₁ (face-top ⁻¹)
    module MiddleVertex = Middle.Framed F₁.Route.endpoint G₀.Route.endpoint MiddleShape.comparison
      F.target-frame G.source-frame (ev₁ ◁ U.Right.First.comparison) (ev₀ ◁ U.Right.Second.comparison)
      F₁.endpoint G₀.endpoint
    module SourceVertex = Source.Framed H₀.Route.endpoint F₀.Route.endpoint SourceShape.comparison
      H.source-frame F.source-frame (ev₀ ◁ U.Right.Long.comparison) (ev₀ ◁ U.Right.First.comparison)
      H₀.endpoint F₀.endpoint
    module TargetVertex = Target.Framed H₁.Route.endpoint G₁.Route.endpoint
      (Shapes.reverse-shape 𝒯 s₁ face-top G₁.Route.endpoint H₁.Route.endpoint TargetShape.comparison)
      H.target-frame G.target-frame (ev₁ ◁ U.Right.Long.comparison) (ev₁ ◁ U.Right.Second.comparison)
      H₁.endpoint G₁.endpoint

    middle-vertex : V.MiddleVertex
    middle-vertex = MiddleVertex.vertex-equation

    source-vertex : V.SourceVertex
    source-vertex = SourceVertex.vertex-equation

    target-vertex : V.TargetVertex
    target-vertex = TargetVertex.vertex-equation

    presentation : CompositePresentation U.arrow (identity-expression ev₁) U.arrow
    presentation = V.presentation middle-vertex source-vertex target-vertex

    comparison : ExpressionIso (compose-expression U.arrow (identity-expression ev₁)) U.arrow
    comparison = V.composite-comparison middle-vertex source-vertex target-vertex
```
