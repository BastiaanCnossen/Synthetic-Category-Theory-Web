# The endpoint edge squares for slices

Pullback cancellation identifies evaluation of a slice arrow with the
corresponding edge of its triangle presentation. Both variances use the
complete endpoint comparison, including its matching identification.

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
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.NormalizedSliceTriangles as Normalized


import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEndpointCones as EndpointCones
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEdgePullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (pullbackCone-isPullback)

module Slice {C : CAT} (x : Obj-abs C) where
  module Endpoint = EndpointCones.Slice 𝒯 M ℱ P I E S Q x
    using (comparison; module Source; module Arrows; module Boundary)
  module Triangle = Normalized.Slice 𝒯 M ℱ P I E S Q x using (vertex)
  module Cancel = Cancellation.Framed.WithComparison 𝒯 P edge₀ ev₁ x Triangle.vertex
    Endpoint.Source.square Endpoint.Source.square-isPullback
    Endpoint.Boundary.point (pullbackCone-isPullback (evaluate vertex₂) x)
    (ev₁ ∘ Endpoint.Arrows.forward) Endpoint.comparison
  open Cancel public using (square; square-isPullback)

module Coslice {C : CAT} (x : Obj-abs C) where
  module Endpoint = EndpointCones.Coslice 𝒯 M ℱ P I E S Q x
    using (comparison; module Source; module Arrows; module Boundary)
  module Triangle = Normalized.Coslice 𝒯 M ℱ P I E S Q x using (vertex)
  module Cancel = Cancellation.Framed.WithComparison 𝒯 P edge₂ ev₀ x Triangle.vertex
    Endpoint.Source.square Endpoint.Source.square-isPullback
    Endpoint.Boundary.point (pullbackCone-isPullback (evaluate vertex₀) x)
    (ev₀ ∘ Endpoint.Arrows.forward) Endpoint.comparison
  open Cancel public using (square; square-isPullback)
```
