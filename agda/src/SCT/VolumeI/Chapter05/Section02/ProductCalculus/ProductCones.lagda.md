# Dependent uncurrying of cones

The matching identification is transported together with the two legs.
Naturality of the postcomposition comparison then transports the
compatibility equation of a cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPostcomposition as Post
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.Cones as Cones
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductCones
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
module SC = Cones S
module TC = Cones T
open Products.DependentProducts P using (Π; uncurry)
open Action W P using (Π-map)
open Identifications W K P using (action; action₂; action-comp)
open Post W K P using (paste; naturality) renaming (comparison to post)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (move-square)

uncurryCone : {X : S.CAT} {B C D : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  → SC.Cone (Π-map f) (Π-map g) X → TC.Cone f g (W.cat X)
uncurryCone {f = f} {g} s = record
  { left = uncurry (SC.Cone.left s) ; right = uncurry (SC.Cone.right s)
  ; match = post g (SC.Cone.right s) ∙
      (action (SC.Cone.match s) ∙ (post f (SC.Cone.left s)) ⁻¹) }

uncurryConeIso : {X : S.CAT} {B C D : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  {s t : SC.Cone (Π-map f) (Π-map g) X}
  → SC.ConeIso s t → TC.ConeIso (uncurryCone s) (uncurryCone t)
uncurryConeIso {f = f} {g} {s} {t} Φ = record
  { leftIso = action α ; rightIso = action β
  ; compatible = paste (τs ∙ fs ⁻¹) (τt ∙ ft ⁻¹) gs gt first third last
      (paste (fs ⁻¹) (ft ⁻¹) τs τt first second third
        (move-square ft second first fs (naturality f α)) rawSquare)
      (naturality g β) }
  where
  α = SC.ConeIso.leftIso Φ
  β = SC.ConeIso.rightIso Φ
  fs = post f (SC.Cone.left s)
  ft = post f (SC.Cone.left t)
  gs = post g (SC.Cone.right s)
  gt = post g (SC.Cone.right t)
  τs = action (SC.Cone.match s)
  τt = action (SC.Cone.match t)
  first = f ◁ action α
  second = action (S._◁_ (Π-map f) α)
  third = action (S._◁_ (Π-map g) β)
  last = g ◁ action β
  rawSquare = (action-comp (SC.Cone.match t) (S._◁_ (Π-map f) α)) ⁻¹ then
    action₂ (SC.ConeIso.compatible Φ) then
    action-comp (S._◁_ (Π-map g) β) (SC.Cone.match s)
```
