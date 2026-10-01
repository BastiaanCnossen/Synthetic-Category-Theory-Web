# The matching of a total cone

The matching obtained by extending the whole pair cone agrees with the
matching assembled from the specified sum compositor and congruence.
Restrict both identifications, collect their endpoint changes, and use
the computation of the chosen sum compositor. Reflection then compares
the original absolute identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.EndpointTransport as Endpoints
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.SumCones as Cones
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumComposition as Composition
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as Cospans
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus as Inverses
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry as Symmetry

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumConeMatching
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (Q : Sums.DependentSums W P) where

private
  module S = View S
  module T = View T
module W = Weakening W
module CS = Cones W K P Q using (module SC; module TC; module Total; module Extension)
open Sums.DependentSums Q using (Σ; pair)
open Action W P Q using (Σ-map; Σ-map-β; Σ-map-cong; Σ-map-comp; flatten-post)
open Identifications W K P Q using (action; action-endpoints; sum-cong-image; reflect-β; reflect₂)
open Composition W K P Q using (composition-image)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Endpoints T
open Inverses T using (inverse-composite; inverse-inverse; pre-inverse)

module Leg {X Y D : T.CAT} (r : T.MAP X Y) (u : T.MAP Y D) where
  a = T.comp-assoc r u (pair D)
  b = T.comp-assoc r (pair Y) (W.map (Σ-map u))
  β = Σ-map-β u ▷ r
  βinv = (Σ-map-β u) ⁻¹ ▷ r
  unit = Σ-map-β (u ∘ r)
  v = W.map (Σ-map u) ◁ Σ-map-β r
  h = flatten-post (Σ-map u) (Σ-map r)
  change = a ∙ (βinv ∙ b ⁻¹)
  boundary = h ⁻¹ ∙ (v ∙ change ⁻¹)

  inverse-change : T._=₂_ (change ⁻¹) (b ∙ (β ∙ a ⁻¹))
  inverse-change = inverse-composite a (βinv ∙ b ⁻¹) then
    isoComp-cong (inverse-composite βinv (b ⁻¹)) (T.idIso (a ⁻¹)) then
    isoComp-cong
      (isoComp-cong (inverse-inverse b)
        ((T.＝-inv ◁ pre-inverse (Σ-map-β u) r) then inverse-inverse β))
      (T.idIso (a ⁻¹)) then isoComp-assoc-at b β (a ⁻¹)

  compositor-normal : T._=₂_ (action (Σ-map-comp r u)) (boundary ∙ unit ⁻¹)
  compositor-normal = composition-image r u then
    isoComp-cong (T.idIso (h ⁻¹))
      (isoComp-cong (T.idIso v)
        (isoComp-cong (T.idIso b) ((isoComp-assoc-at β (a ⁻¹) (unit ⁻¹)) ⁻¹) then
          (isoComp-assoc-at b (β ∙ a ⁻¹) (unit ⁻¹)) ⁻¹) then
        (isoComp-assoc-at v (b ∙ (β ∙ a ⁻¹)) (unit ⁻¹)) ⁻¹ then
        isoComp-cong (isoComp-cong (T.idIso v) (inverse-change ⁻¹)) (T.idIso (unit ⁻¹))) then
    (isoComp-assoc-at (h ⁻¹) (v ∙ change ⁻¹) (unit ⁻¹)) ⁻¹

  boundary-image : T._=₂_ (action (Σ-map-comp r u) ∙ unit) boundary
  boundary-image = isoComp-cong compositor-normal (T.idIso unit) then
    isoComp-assoc-at boundary (unit ⁻¹) unit then
    isoComp-cong (T.idIso boundary) (isoComp-inverseˡ-at unit) then isoComp-unitʳ-at boundary

module Matching (PT : Pullbacks.PullbackStructure T)
  {B C D Z : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (s : CS.TC.Cone f g Z) where

  module Total = CS.Total PT s using (cospan; pairCone; cone)
  module Extended = CS.Extension Total.pairCone using (rawMatch)
  module Map = Cospans.Action T PT Total.cospan using (module Normalization)
  module Left = Leg (CS.TC.Cone.left s) f
  module Right = Leg (CS.TC.Cone.right s) g
  τ = pair D ◁ CS.TC.Cone.match s

  direct : S._=₁_ (S._∘_ (Σ-map f) (Σ-map (CS.TC.Cone.left s)))
    (S._∘_ (Σ-map g) (Σ-map (CS.TC.Cone.right s)))
  direct = Endpoints.changeEndpoints S
    (Σ-map-comp (CS.TC.Cone.left s) f) (Σ-map-comp (CS.TC.Cone.right s) g)
    (Σ-map-cong (CS.TC.Cone.match s))

  direct-image : T._=₂_ (action direct) (changeEndpoints Left.boundary Right.boundary τ)
  direct-image = action-endpoints _ _ _ then
    changeEndpoints-cong _ _ (sum-cong-image (CS.TC.Cone.match s)) then
    changeEndpoints-successive Left.unit Right.unit
      (action (Σ-map-comp (CS.TC.Cone.left s) f))
      (action (Σ-map-comp (CS.TC.Cone.right s) g)) τ then
    changeEndpoints-boundaries τ Left.boundary-image Right.boundary-image

  pair-image : T._=₂_ (CS.TC.Cone.match Total.pairCone)
    (changeEndpoints (Left.change ⁻¹) (Right.change ⁻¹) τ)
  pair-image = (Map.Normalization.matching s) ⁻¹ then
    isoComp-cong (T.idIso (Right.change ⁻¹))
      (isoComp-cong (T.idIso τ) ((inverse-inverse Left.change) ⁻¹))

  reflected-image : T._=₂_ Extended.rawMatch (changeEndpoints Left.boundary Right.boundary τ)
  reflected-image = isoComp-cong (T.idIso (Right.h ⁻¹))
      (isoComp-cong (changeEndpoints-cong Left.v Right.v pair-image)
        ((inverse-inverse Left.h) ⁻¹)) then
    changeEndpoints-cong (Left.h ⁻¹) (Right.h ⁻¹)
      (changeEndpoints-successive (Left.change ⁻¹) (Right.change ⁻¹) Left.v Right.v τ) then
    changeEndpoints-successive (Left.v ∙ Left.change ⁻¹) (Right.v ∙ Right.change ⁻¹)
      (Left.h ⁻¹) (Right.h ⁻¹) τ

  matching : S._=₂_ (CS.SC.Cone.match Total.cone) direct
  matching = reflect₂ (reflect-β Extended.rawMatch then reflected-image then direct-image ⁻¹)

  cone : CS.SC.Cone (Σ-map f) (Σ-map g) (Σ Z)
  cone = record
    { left = Σ-map (CS.TC.Cone.left s) ; right = Σ-map (CS.TC.Cone.right s) ; match = direct }

  comparison : CS.SC.ConeIso Total.cone cone
  comparison = Symmetry.cone-match-change S _ _ _ _ matching
```
