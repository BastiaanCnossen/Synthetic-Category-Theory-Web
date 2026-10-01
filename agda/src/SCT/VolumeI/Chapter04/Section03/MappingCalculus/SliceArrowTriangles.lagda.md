# Arrows in a slice as triangles with a fixed vertex

The constant-side square theorem identifies the square presentation of
arrows in a slice with triangles whose last vertex is fixed. Dually,
arrows in a coslice correspond to triangles with fixed first vertex.
Both comparisons follow by pullback pasting and retain their cone data.
Identifying directed evaluation with the corresponding Segal map is a
separate step.

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
import SCT.VolumeI.Chapter02.Section02.TrianglePullbacks as TriangleSquares
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceArrowSquares as ArrowSquares
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.MappedConeComparisons as Evaluated
import SCT.VolumeI.Chapter01.Section06.Pasting.VerticalPasting as Vertical
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as Cospans
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.NormalizedSliceTriangles as Normalized

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceArrowTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S using (Triangles; vertex₀; vertex₂)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; IsPullback; pullbackCone-isPullback; conePre;
    coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)

module Vertex {C : CAT} (x : Obj-abs C) (u : Obj-abs [1])
  (w : Cone (funPre (insert u)) (identityArrow {C}) (Triangles C)) (ew : IsPullback w) where
  module SquaresAt = ArrowSquares.Endpoint 𝒯 M ℱ P I C u x
    using (side; constant-point; category; change; module Change; module Fixed; module ToArrows)
  category = Pullback (Cone.right w) x
  module Paste = Vertical.Vertical 𝒯 P x identityArrow (funPre (insert u))
    w (pullbackCone (Cone.right w) x) ew using (square; square-isPullback)
  square : Cone SquaresAt.side SquaresAt.constant-point category
  square = Paste.square

  abstract
    square-isPullback : IsPullback square
    square-isPullback = Paste.square-isPullback (pullbackCone-isPullback (Cone.right w) x)

  to-squares : MAP category SquaresAt.category
  to-squares = pullbackLift square
  square-comparison = pullbackLift-β square
  module Image = SquaresAt.Fixed.At square using (simplified; comparison; module L; module R)

  module ToArrows {T : CAT} (s : Cone (evaluate u) x T) (es : IsPullback s) where
    module Arrows = SquaresAt.ToArrows s es
      using (forward; isEquiv; mapped; image; comparison)
    forward : MAP category (Ar T)
    forward = Arrows.forward ∘ to-squares

    isEquiv : IsEquiv forward
    isEquiv = equiv-compose to-squares Arrows.forward square-isPullback Arrows.isEquiv

    comparison : ConeIso (conePre forward Arrows.mapped) (conePre to-squares Arrows.image)
    comparison = coneIso-compose (coneIso-pre to-squares Arrows.comparison)
      (coneIso-inverse (conePre-assoc to-squares Arrows.forward Arrows.mapped))

    module ChangeAction = Cospans.Action 𝒯 P SquaresAt.change using (map-iso; map-pre)
    direct-image = SquaresAt.Change.mapCone square

    direct-comparison : ConeIso (conePre forward Arrows.mapped) direct-image
    direct-comparison = coneIso-compose (ChangeAction.map-iso square-comparison)
      (coneIso-compose
        (coneIso-inverse (ChangeAction.map-pre to-squares
          (pullbackCone SquaresAt.side SquaresAt.constant-point))) comparison)

    normalized-comparison : ConeIso (conePre forward Arrows.mapped) Image.simplified
    normalized-comparison = coneIso-compose Image.comparison direct-comparison

    module AtEndpoint (v : Obj-abs [1]) = Evaluated.At 𝒯 M ℱ P v s forward
      Image.simplified normalized-comparison using (evaluated; comparison)

module SliceAt {C : CAT} (x : Obj-abs C) where
  module Triangle = Normalized.Slice 𝒯 M ℱ P I E S Q x
    using (square; square-isPullback)
  module Source = SliceEndpoint x using (square; square-isPullback)
  module Presentation = Vertex x one Triangle.square Triangle.square-isPullback
    using (module ToArrows)
  open Presentation.ToArrows Source.square Source.square-isPullback public

module CosliceAt {C : CAT} (x : Obj-abs C) where
  module Triangle = Normalized.Coslice 𝒯 M ℱ P I E S Q x
    using (square; square-isPullback)
  module Source = CosliceEndpoint x using (square; square-isPullback)
  module Presentation = Vertex x zero Triangle.square Triangle.square-isPullback
    using (module ToArrows)
  open Presentation.ToArrows Source.square Source.square-isPullback public
```
