# The corner equation for double currying

The comparison between the two orders of evaluating a corner retains the
reflected side comparisons and their uncurried images. Its coordinate
part is the actual five-factor matching of the currying permutation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.DoubleEvaluationCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter02.Section02.DirectUnitTriangles 𝒯 M ℱ P I E using (module ReflectedEndpoint)
import SCT.VolumeI.Chapter02.Section02.SquareCurrying as Currying
import SCT.VolumeI.Chapter02.Section02.SquareCurryingCoordinates as Axes
import SCT.VolumeI.Chapter02.Section02.DoubleEvaluationCoordinates as Coordinates
import SCT.VolumeI.Chapter02.Section02.CurryRestrictionCorner as Restriction
import SCT.VolumeI.Chapter02.Section02.CurryPostcomposition as Postcomposition
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

pre-chain : {X Y Z : CAT} {f g h : MAP Y Z} (α : g =₁ h) (β : f =₁ g)
  (r : MAP X Y) {s : MAP X Z} (tail : s =₁ (f ∘ r)) →
  (((α ∙ β) ▷ r) ∙ tail) =₂ ((α ▷ r) ∙ ((β ▷ r) ∙ tail))
pre-chain α β r tail = isoComp-assoc-at (α ▷ r) (β ▷ r) tail ∙
  isoComp-cong (preWhisker-isoComp-at α β r) (idIso tail)

module At {Γ A B C : CAT} (W : MAP Γ (Fun (A × B) C))
  (u : Obj-abs A) (v : Obj-abs B) where
  module Curried = Currying.At 𝒯 M ℱ W
  module H = Curried.Horizontal u
  module V = Curried.Vertical v
  module Coord = Coordinates.At 𝒯 M ℱ Curried.H u v
  module Inner = Restriction.At 𝒯 M ℱ Curried.diagram (insert v) u
  module Outer = Postcomposition.Evaluation 𝒯 M ℱ P I E (evaluate u) Curried.first-curry v
  h = Curried.H
  ia = insert {X = Γ} u
  ib = insert {X = Γ} v
  qH = funPre-uncurry (Axes.coinsert 𝒯 M ℱ u) W
  qV = funPre-uncurry (insert v) W
  aH = comp-assoc H.Coordinate.step Curried.Coordinates.permute h
  aV = comp-assoc V.Coordinate.step Curried.Coordinates.permute h
  headH = h ◁ H.Coordinate.comparison
  headV = h ◁ V.Coordinate.comparison
  curry-edge = evaluate-curry u Curried.diagram
  θH = headH ∙ (aH ∙ (curry-edge ∙ Outer.raw))
  θV = headV ∙ (aV ∙ Inner.raw)
  module RefH = ReflectedEndpoint v H.evaluated H.side qH θH H.comparison H.comparison-β
  module RefV = ReflectedEndpoint u (Curried.first-curry ∘ ib) V.side qV θV V.restricted V.restricted-β
  left = (qH ▷ ib) ∙ evaluate-uncurry v H.side
  right = (qV ▷ ia) ∙ evaluate-uncurry u V.side
  outer-endpoint = evaluate-uncurry v H.evaluated
  inner-endpoint = evaluate-uncurry u (Curried.first-curry ∘ ib)
  outer-tail = (Outer.raw ▷ ib) ∙ outer-endpoint
  inner-tail = (Inner.raw ▷ ia) ∙ inner-endpoint
  outer-boundary = (evaluate u ◁ evaluate-curry v Curried.first-curry) ∙
    evaluate-post-at v (evaluate u) Curried.nested
  boundary = (evaluate u ◁ V.boundary) ∙ evaluate-post-at v (evaluate u) Curried.nested
  top = curry-edge ▷ ib
  middle = comp-assoc ib Curried.first-curry (evaluate u)
  vhead = headV ▷ ia
  va = aV ▷ ia
  hhead = headH ▷ ib
  ha = aH ▷ ib
  horizontal-normal = hhead ∙ (ha ∙ (top ∙ outer-tail))
  vertical-normal = vhead ∙ (va ∙ inner-tail)

  abstract
    horizontal-image : (left ∙ (evaluate v ◁ H.comparison)) =₂ horizontal-normal
    horizontal-image = isoComp-cong (idIso hhead)
        (isoComp-cong (idIso ha) (pre-chain curry-edge Outer.raw ib outer-endpoint) ∙
          pre-chain aH (curry-edge ∙ Outer.raw) ib outer-endpoint) ∙
      pre-chain headH (aH ∙ (curry-edge ∙ Outer.raw)) ib outer-endpoint ∙ RefH.endpoint

    vertical-image : (right ∙ (evaluate u ◁ V.restricted)) =₂ vertical-normal
    vertical-image = isoComp-cong (idIso vhead) (pre-chain aV Inner.raw ia inner-endpoint) ∙
      pre-chain headV (aV ∙ Inner.raw) ia inner-endpoint ∙ RefV.endpoint

    boundary-image : (right ∙ boundary) =₂ (vertical-normal ∙ outer-boundary)
    boundary-image = isoComp-cong vertical-image (idIso outer-boundary) ∙
      (isoComp-assoc-at right (evaluate u ◁ V.restricted) outer-boundary) ⁻¹ ∙
      isoComp-cong (idIso right)
        (isoComp-assoc-at (evaluate u ◁ V.restricted)
          (evaluate u ◁ evaluate-curry v Curried.first-curry)
          (evaluate-post-at v (evaluate u) Curried.nested) ∙
        isoComp-cong (postWhisker-isoComp-at (evaluate u) V.restricted
          (evaluate-curry v Curried.first-curry))
          (idIso (evaluate-post-at v (evaluate u) Curried.nested)))

    interior : (inner-tail ∙ outer-boundary) =₂ (Coord.E₂ ∙ (top ∙ outer-tail))
    interior = isoComp-assoc-at Coord.E₂ top outer-tail ∙
      isoComp-cong (idIso (Coord.E₂ ∙ top)) (cancel-left middle outer-tail) ∙
      isoComp-assoc-at (Coord.E₂ ∙ top) (middle ⁻¹) (middle ∙ outer-tail) ∙
      isoComp-cong Inner.comparison (Outer.comparison ⁻¹)

    comparison : (right ∙ boundary) =₂
      (Coord.result ∙ (left ∙ (evaluate v ◁ H.comparison)))
    comparison = isoComp-cong (idIso Coord.result) (horizontal-image ⁻¹) ∙
      isoComp-cong (idIso Coord.result) (isoComp-assoc-at hhead ha (top ∙ outer-tail)) ∙
      isoComp-assoc-at Coord.result (hhead ∙ ha) (top ∙ outer-tail) ∙
      isoComp-cong Coord.comparison (idIso (top ∙ outer-tail)) ∙
      (isoComp-assoc-at vhead (va ∙ Coord.E₂) (top ∙ outer-tail)) ⁻¹ ∙
      isoComp-cong (idIso vhead) ((isoComp-assoc-at va Coord.E₂ (top ∙ outer-tail)) ⁻¹) ∙
      isoComp-cong (idIso vhead) (isoComp-cong (idIso va) interior) ∙
      isoComp-cong (idIso vhead) (isoComp-assoc-at va inner-tail outer-boundary) ∙
      isoComp-assoc-at vhead (va ∙ inner-tail) outer-boundary ∙ boundary-image
```
