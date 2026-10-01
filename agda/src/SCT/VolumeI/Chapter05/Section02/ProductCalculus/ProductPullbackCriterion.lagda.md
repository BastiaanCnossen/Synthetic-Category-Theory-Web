# A lifting criterion for dependent pullbacks

If uncurrying of whole cones commutes with restriction, the dependent
product preserves pullbacks. This module separates that lifting argument
from the finite coherence calculation. `ProductConeRestriction` constructs
the restriction comparison, and `ProductPullbacks` applies this criterion.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductCones as Cones
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductConeCurrying as Currying
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductConeReflection as Reflection
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackSquares as Squares
import SCT.VolumeI.Chapter01.Section06.PullbackCriterion as Criterion
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction as ConeAction

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPullbackCriterion
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (PS : Pullbacks.PullbackStructure S) (PT : Pullbacks.PullbackStructure T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module SS = Squares S PS
module TS = Squares T PT
module PS = Pullbacks.PullbackStructure PS
open Products.DependentProducts P using (Π; evaluation; curry; curry-β; uncurry)
open Action W P using (Π-map; reflect)
open Cones W K P using (module SC; module TC; uncurryCone; uncurryConeIso)
open T using (_∘_)

Restriction : Set l
Restriction = {X Y : S.CAT} {B C D : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (h : S.MAP X Y) (s : SC.Cone (Π-map f) (Π-map g) Y)
  → TC.ConeIso (uncurryCone (SC.conePre h s)) (TC.conePre (W.map h) (uncurryCone s))

module FromRestriction (restriction : Restriction)
  {B C D Z : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (s : TC.Cone f g Z) (universal : TS.IsPullback s) where

  module Known = TS.UniversalCone s universal using (factor; factor-β; reflect)
  module Curried = Currying.CurryCone W K P (TC.conePre (evaluation Z) s)
    using (value; comparison)

  square : SC.Cone (Π-map f) (Π-map g) (Π Z)
  square = Curried.value

  evaluation-comparison : {X : S.CAT} (h : S.MAP X (Π Z))
    → TC.ConeIso (uncurryCone (SC.conePre h square)) (TC.conePre (uncurry h) s)
  evaluation-comparison h = TS.coneIso-compose
    (TS.conePre-assoc (W.map h) (evaluation Z) s)
    (TS.coneIso-compose (TS.coneIso-pre (W.map h) Curried.comparison) (restriction h square))

  factor : {X : S.CAT} → SC.Cone (Π-map f) (Π-map g) X → S.MAP X (Π Z)
  factor t = curry (Known.factor (uncurryCone t))

  factor-β : {X : S.CAT} (t : SC.Cone (Π-map f) (Π-map g) X)
    → SC.ConeIso (SC.conePre (factor t) square) t
  factor-β t = Reflection.ReflectCone.comparison W K P _ t
    (TS.coneIso-compose (Known.factor-β (uncurryCone t))
      (TS.coneIso-compose (ConeAction.cone-action T s (T._⁻¹ (curry-β (Known.factor (uncurryCone t)))))
        (evaluation-comparison (factor t))))

  reflect-cones : {X : S.CAT} (h k : S.MAP X (Π Z))
    → SC.ConeIso (SC.conePre h square) (SC.conePre k square) → S._=₁_ h k
  reflect-cones h k Φ = reflect (Known.reflect (uncurry h) (uncurry k)
    (TS.coneIso-compose (evaluation-comparison k)
      (TS.coneIso-compose (uncurryConeIso Φ) (TS.coneIso-inverse (evaluation-comparison h)))))

  square-isPullback : SS.IsPullback square
  square-isPullback = Criterion.cone-isPullback-from-lifting S PS square
    (factor (PS.pullbackCone (Π-map f) (Π-map g)))
    (factor-β (PS.pullbackCone (Π-map f) (Π-map g))) reflect-cones
```
