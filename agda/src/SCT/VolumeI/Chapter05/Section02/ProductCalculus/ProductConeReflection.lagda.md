# Reflecting comparisons of dependent cones

Reflection first lifts the two leg identifications. The computation rule
replaces their local images by the prescribed legs. Naturality and
reflection of identifications between identifications then lift the
compatibility equation.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPostcomposition as Post
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductCones as Cones
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons as ConeCalculus
import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport as Endpoint

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductConeReflection
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P using (Π; uncurry)
open Action W P using (Π-map)
open Identifications W K P using (action; action-comp; reflect; reflect-β; reflect₂)
open Post W K P using (naturality) renaming (comparison to post)
open Cones W K P using (module SC; module TC; uncurryCone)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open ConeCalculus T using (coneIso-adjust)
open Endpoint T

module ReflectCone {X : S.CAT} {B C D : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (s t : SC.Cone (Π-map f) (Π-map g) X)
  (Φ : TC.ConeIso (uncurryCone s) (uncurryCone t)) where

  left = reflect (TC.ConeIso.leftIso Φ)
  right = reflect (TC.ConeIso.rightIso Φ)
  adjusted = coneIso-adjust Φ (action left) (action right)
    ((reflect-β (TC.ConeIso.leftIso Φ)) ⁻¹)
    ((reflect-β (TC.ConeIso.rightIso Φ)) ⁻¹)
  fs = post f (SC.Cone.left s)
  ft = post f (SC.Cone.left t)
  gs = post g (SC.Cone.right s)
  gt = post g (SC.Cone.right t)
  τs = action (SC.Cone.match s)
  τt = action (SC.Cone.match t)
  α = action (S._◁_ (Π-map f) left)
  β = action (S._◁_ (Π-map g) right)

  rawSquare : T._=₂_ (τt ∙ α) (β ∙ τs)
  rawSquare = changeEndpoints-reflect fs gt _ _
    (changeEndpoints-comp fs gs gt β τs ∙
    (isoComp-cong
      ((square-to-changeEndpoints gs gt β (g ◁ action right) (naturality g right)) ⁻¹)
      (T.idIso (TC.Cone.match (uncurryCone s))) ∙
    (TC.ConeIso.compatible adjusted ∙
    (isoComp-cong (T.idIso (TC.Cone.match (uncurryCone t)))
      (square-to-changeEndpoints fs ft α (f ◁ action left) (naturality f left)) ∙
      (changeEndpoints-comp fs ft gt τt α) ⁻¹))))

  comparison : SC.ConeIso s t
  comparison = record
    { leftIso = left ; rightIso = right
    ; compatible = reflect₂
        ((action-comp (S._◁_ (Π-map g) right) (SC.Cone.match s)) ⁻¹ ∙
          (rawSquare ∙ action-comp (SC.Cone.match t) (S._◁_ (Π-map f) left))) }
```
