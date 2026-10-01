# The absorbing corners of the evaluation deformations

At the absorbing endpoint, both routes around each corner are
identifications with the same initial or terminal object. Their uniqueness
supplies the full shape equation required for the restriction-cone
comparison. This uses Segal, the commutative-square axiom, and Rezk; no
functoriality of universals is assumed.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformationCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationDeformationDiagrams 𝒯 M ℱ P I E
  using (maximum-absorbing; minimum-absorbing)
open import SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.IdentificationUniqueness 𝒯 M ℱ P I E S Q R
  using (terminal-Iso₂; initial-Iso₂)
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates 𝒯 M ℱ using (coinsert)
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionBoundaryCorners as Boundaries
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.InsertedShapeCorners as Vertices

module MaximumCorner (C : CAT) (v : Obj-abs [1]) (k : MAP [1] [1])
  (β : (max ∘ insert v) =₁ k) (e : (k ∘ one) =₁ one) where
  δ = Vertices.Vertex.corner 𝒯 M ℱ one v
  b = constant-boundary v one
  ε = e ⁻¹ ∙ b
  module Left = Boundaries.Edge 𝒯 M ℱ P {C = C} (coinsert one) max (const one) maximum-absorbing v
    using (vertex)
  module Right = Boundaries.Edge 𝒯 M ℱ P {C = C} (insert v) max k β one
    using (vertex)
  abstract
    shape : (ε ∙ Left.vertex) =₂ (Right.vertex ∙ (max ◁ δ))
    shape = terminal-Iso₂ one one-isTerminal e _ _
  module Result = Boundaries.Corner 𝒯 M ℱ P {C = C} v one
    (coinsert one) (insert v) max δ (const one) k maximum-absorbing β ε shape
    using (comparison; compatible; module L; module R; outer)

module MinimumCorner (C : CAT) (v : Obj-abs [1]) (k : MAP [1] [1])
  (β : (min ∘ insert v) =₁ k) (e : (k ∘ zero) =₁ zero) where
  δ = Vertices.Vertex.corner 𝒯 M ℱ zero v
  b = constant-boundary v zero
  ε = e ⁻¹ ∙ b
  module Left = Boundaries.Edge 𝒯 M ℱ P {C = C} (coinsert zero) min (const zero) minimum-absorbing v
    using (vertex)
  module Right = Boundaries.Edge 𝒯 M ℱ P {C = C} (insert v) min k β zero
    using (vertex)
  abstract
    shape : (ε ∙ Left.vertex) =₂ (Right.vertex ∙ (min ◁ δ))
    shape = initial-Iso₂ zero zero-isInitial ((b ∙ Left.vertex) ⁻¹) _ _
  module Result = Boundaries.Corner 𝒯 M ℱ P {C = C} v zero
    (coinsert zero) (insert v) min δ (const zero) k minimum-absorbing β ε shape
    using (comparison; compatible; module L; module R; outer)

module MaximumSource (C : CAT) = MaximumCorner C zero (id [1]) max-right-zero (comp-unitˡ one)
module MaximumTarget (C : CAT) = MaximumCorner C one (const one) max-right-one (constant-boundary one one)
module MinimumSource (C : CAT) = MinimumCorner C zero (const zero) min-right-zero (constant-boundary zero zero)
module MinimumTarget (C : CAT) = MinimumCorner C one (id [1]) min-right-one (comp-unitˡ zero)
```

The normalized restriction endpoints also give the corner equations after
evaluation. These equations retain the constant-arrow frames and are the
inputs to the comparison of evaluated expressions.

```agda
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.EvaluationRestrictionEndpoints as EndpointsOfRestriction
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionCornerTransport as Transport

module Evaluated (C : CAT) where
  module Upper = EndpointsOfRestriction.At.Constant 𝒯 M ℱ P I E C
    (coinsert one) max one maximum-absorbing
  module Lower = EndpointsOfRestriction.At.Constant 𝒯 M ℱ P I E C
    (coinsert zero) min zero minimum-absorbing

  module MaximumSourceFrame where
    module H = Upper zero
    module V = EndpointsOfRestriction.At.Identity 𝒯 M ℱ P I E C (insert zero) max max-right-zero one
    δ = Vertices.Vertex.corner 𝒯 M ℱ one zero
    module T = Transport.At 𝒯 M ℱ P {C = C} zero one (coinsert one) (insert zero) max δ
    abstract
      shape : H.Route.endpoint =₂ (V.Route.endpoint ∙ (max ◁ δ))
      shape = terminal-Iso₂ one one-isTerminal (idIso one) _ _
    module Normalized = T.Framed H.Route.endpoint V.Route.endpoint shape
      H.frame (comp-unitʳ (ev₁ {C}))
      (ev₀ ◁ H.N.direct) (ev₁ ◁ V.N.direct) H.endpoint V.endpoint
    horizontal-direct = H.N.direct
    vertical-direct = V.N.direct
    corner-matching = T.matching
    abstract
      comparison : (H.frame ∙ (ev₀ ◁ H.N.direct)) =₂
        ((comp-unitʳ (ev₁ {C}) ∙ (ev₁ ◁ V.N.direct)) ∙ T.matching)
      comparison = Normalized.framed

  module MaximumTargetFrame where
    module H = Upper one
    module V = EndpointsOfRestriction.At.Constant 𝒯 M ℱ P I E C (insert one) max one max-right-one one
    δ = Vertices.Vertex.corner 𝒯 M ℱ one one
    module T = Transport.At 𝒯 M ℱ P {C = C} one one (coinsert one) (insert one) max δ
    abstract
      shape : H.Route.endpoint =₂ (V.Route.endpoint ∙ (max ◁ δ))
      shape = terminal-Iso₂ one one-isTerminal (idIso one) _ _
    module Normalized = T.Framed H.Route.endpoint V.Route.endpoint shape
      H.frame V.frame (ev₁ ◁ H.N.direct) (ev₁ ◁ V.N.direct) H.endpoint V.endpoint
    horizontal-direct = H.N.direct
    vertical-direct = V.N.direct
    corner-matching = T.matching
    abstract
      comparison : (H.frame ∙ (ev₁ ◁ H.N.direct)) =₂
        ((V.frame ∙ (ev₁ ◁ V.N.direct)) ∙ T.matching)
      comparison = Normalized.framed

  module MinimumSourceFrame where
    module H = Lower zero
    module V = EndpointsOfRestriction.At.Constant 𝒯 M ℱ P I E C (insert zero) min zero min-right-zero zero
    δ = Vertices.Vertex.corner 𝒯 M ℱ zero zero
    module T = Transport.At 𝒯 M ℱ P {C = C} zero zero (coinsert zero) (insert zero) min δ
    abstract
      shape : H.Route.endpoint =₂ (V.Route.endpoint ∙ (min ◁ δ))
      shape = initial-Iso₂ zero zero-isInitial (H.Route.endpoint ⁻¹) _ _
    module Normalized = T.Framed H.Route.endpoint V.Route.endpoint shape
      H.frame V.frame (ev₀ ◁ H.N.direct) (ev₀ ◁ V.N.direct) H.endpoint V.endpoint
    horizontal-direct = H.N.direct
    vertical-direct = V.N.direct
    corner-matching = T.matching
    abstract
      comparison : (H.frame ∙ (ev₀ ◁ H.N.direct)) =₂
        ((V.frame ∙ (ev₀ ◁ V.N.direct)) ∙ T.matching)
      comparison = Normalized.framed

  module MinimumTargetFrame where
    module H = Lower one
    module V = EndpointsOfRestriction.At.Identity 𝒯 M ℱ P I E C (insert one) min min-right-one zero
    δ = Vertices.Vertex.corner 𝒯 M ℱ zero one
    module T = Transport.At 𝒯 M ℱ P {C = C} one zero (coinsert zero) (insert one) min δ
    abstract
      shape : H.Route.endpoint =₂ (V.Route.endpoint ∙ (min ◁ δ))
      shape = initial-Iso₂ zero zero-isInitial (H.Route.endpoint ⁻¹) _ _
    module Normalized = T.Framed H.Route.endpoint V.Route.endpoint shape
      H.frame (comp-unitʳ (ev₀ {C}))
      (ev₁ ◁ H.N.direct) (ev₀ ◁ V.N.direct) H.endpoint V.endpoint
    horizontal-direct = H.N.direct
    vertical-direct = V.N.direct
    corner-matching = T.matching
    abstract
      comparison : (H.frame ∙ (ev₁ ◁ H.N.direct)) =₂
        ((comp-unitʳ (ev₀ {C}) ∙ (ev₀ ◁ V.N.direct)) ∙ T.matching)
      comparison = Normalized.framed
```
