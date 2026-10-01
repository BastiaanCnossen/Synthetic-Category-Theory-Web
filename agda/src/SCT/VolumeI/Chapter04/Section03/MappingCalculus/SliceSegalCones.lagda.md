# The Segal cone in slice-arrow coordinates

The curried square comparison, restricted to the triangle presentation,
has the specified edge frame as its endpoint leg. The full matching and
that leg computation are both retained for pullback pasting.

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

import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceEndpointMatchings as Matchings

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceSegalCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S
open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I using (module Criterion)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)

module Slice {C : CAT} (x : Obj-abs C) where
  module Triangle = Normalized.Slice 𝒯 M ℱ P I E S Q x
    using (nested; k; restriction; edge; module Endpoint; module Corner)
  module Boundary = Matchings.Slice 𝒯 M ℱ P I E S Q x
    using (t; image; module LeftParameter)
  open Boundary using (t; image)
  square = Criterion.target-square (ev₀ {C})
  segal = triangle-cone C

  triangle-comparison : ConeIso (conePre Triangle.nested square) segal
  triangle-comparison = coneIso-compose (conePre-id segal)
    (coneIso-compose (cone-action segal Triangle.restriction)
    (coneIso-compose (conePre-assoc Triangle.k _ segal)
    (coneIso-compose (coneIso-pre Triangle.k Triangle.Corner.comparison)
      (coneIso-inverse (conePre-assoc Triangle.k Triangle.Endpoint.nested square)))))

  θ = comp-assoc t Triangle.k Triangle.Endpoint.nested

  raw : ConeIso (conePre (Cone.left image) square) (conePre t segal)
  raw = coneIso-compose (coneIso-pre t triangle-comparison)
    (coneIso-compose (coneIso-inverse (conePre-assoc t Triangle.nested square))
      (cone-action square (θ ⁻¹)))

  abstract
    right-frame : ConeIso.rightIso raw =₂ Boundary.LeftParameter.boundary′
    right-frame =
      (isoComp-assoc-at (Triangle.edge ▷ t)
        ((comp-assoc t Triangle.nested ev₁) ⁻¹) ((ev₁ ◁ θ) ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso (Triangle.edge ▷ t))
        (isoComp-cong (idIso ((comp-assoc t Triangle.nested ev₁) ⁻¹)) (post-inverse ev₁ θ))

  comparison : ConeIso (conePre (Cone.left image) square) (conePre t segal)
  comparison = coneIso-adjust raw (ConeIso.leftIso raw) Boundary.LeftParameter.boundary′
    (idIso _) right-frame

module Coslice {C : CAT} (x : Obj-abs C) where
  module Triangle = Normalized.Coslice 𝒯 M ℱ P I E S Q x
    using (nested; k; restriction; edge; module Endpoint; module Corner)
  module Boundary = Matchings.Coslice 𝒯 M ℱ P I E S Q x
    using (t; image; module LeftParameter)
  open Boundary using (t; image)
  square = Criterion.source-square (ev₁ {C})
  segal = coneSwap (triangle-cone C)

  triangle-comparison : ConeIso (conePre Triangle.nested square) segal
  triangle-comparison = coneIso-compose (conePre-id segal)
    (coneIso-compose (cone-action segal Triangle.restriction)
    (coneIso-compose (conePre-assoc Triangle.k _ segal)
    (coneIso-compose (coneIso-pre Triangle.k Triangle.Corner.comparison)
      (coneIso-inverse (conePre-assoc Triangle.k Triangle.Endpoint.nested square)))))

  θ = comp-assoc t Triangle.k Triangle.Endpoint.nested

  raw : ConeIso (conePre (Cone.left image) square) (conePre t segal)
  raw = coneIso-compose (coneIso-pre t triangle-comparison)
    (coneIso-compose (coneIso-inverse (conePre-assoc t Triangle.nested square))
      (cone-action square (θ ⁻¹)))

  abstract
    right-frame : ConeIso.rightIso raw =₂ Boundary.LeftParameter.boundary′
    right-frame =
      (isoComp-assoc-at (Triangle.edge ▷ t)
        ((comp-assoc t Triangle.nested ev₀) ⁻¹) ((ev₀ ◁ θ) ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso (Triangle.edge ▷ t))
        (isoComp-cong (idIso ((comp-assoc t Triangle.nested ev₀) ⁻¹)) (post-inverse ev₀ θ))

  comparison : ConeIso (conePre (Cone.left image) square) (conePre t segal)
  comparison = coneIso-adjust raw (ConeIso.leftIso raw) Boundary.LeftParameter.boundary′
    (idIso _) right-frame

```
