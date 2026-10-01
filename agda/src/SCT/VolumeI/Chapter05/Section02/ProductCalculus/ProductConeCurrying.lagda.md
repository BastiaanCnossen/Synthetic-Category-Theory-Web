# Dependent currying of cones

Currying the matching uses reflection with its computation identification.
This gives a comparison of whole cones, including the equation relating
the prescribed matching to the uncurried one.

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
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry as Symmetry
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductConeCurrying
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P using (Π; curry; curry-β; uncurry)
open Action W P using (Π-map)
open Identifications W K P using (action; reflect; reflect-β)
open Post W K P using () renaming (comparison to post)
open Cones W K P using (module SC; module TC; uncurryCone)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open ConeCalculus T using (coneRetarget; coneRetarget-β; coneIso-compose; coneIso-inverse)
open Symmetry T using (cone-match-change)
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (cancel-right)
open Iso T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (cancel-inverse)

module CurryCone {X : S.CAT} {B C D : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (s : TC.Cone f g (W.cat X)) where

  left = curry (TC.Cone.left s)
  right = curry (TC.Cone.right s)
  left-β = (curry-β (TC.Cone.left s)) ⁻¹
  right-β = (curry-β (TC.Cone.right s)) ⁻¹
  wanted = coneRetarget s (uncurry left) (uncurry right) (left-β ⁻¹) (right-β ⁻¹)
  desired = TC.Cone.match wanted
  leftChange = post f left
  rightChange = post g right
  rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

  value : SC.Cone (Π-map f) (Π-map g) X
  value = record { left = left ; right = right ; match = reflect rawMatch }

  match-β : T._=₂_ (TC.Cone.match (uncurryCone value)) desired
  match-β = cancel-right leftChange desired ∙
    (isoComp-cong (cancel-inverse rightChange (desired ∙ leftChange)) (T.idIso (leftChange ⁻¹)) ∙
    ((isoComp-assoc-at rightChange rawMatch (leftChange ⁻¹)) ⁻¹ ∙
      isoComp-cong (T.idIso rightChange)
        (isoComp-cong (reflect-β rawMatch) (T.idIso (leftChange ⁻¹)))))

  abstract
    comparison : TC.ConeIso (uncurryCone value) s
    comparison = coneIso-compose
      (coneIso-inverse (coneRetarget-β s _ _ (left-β ⁻¹) (right-β ⁻¹)))
      (cone-match-change _ _ _ _ match-β)
```
