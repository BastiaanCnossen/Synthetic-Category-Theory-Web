# Preservation of functor categories

The category comparison and its evaluation square are primitive
preservation data. Compatibility with uncurrying follows from that square
and naturality of the product comparison. The parameter category is
arbitrary throughout.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as Products
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ProductNaturality as ProductNaturality
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section07.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps

module SCT.VolumeI.Chapter05.Section01.FunctorPreservation
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT) where

private
  module S = View S
  module T = View T
module W = Weakening W
module FS = Functors.FunctorCategories FS
module FT = Functors.FunctorCategories FT
module SC = Currying S MS FS using (funUncurry; funCurry; funCurry-β)
module TC = Currying T MT FT using (funUncurry; funUncurry-restrict; funCurry; funCurry-β; funReflect)
module SP = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (productMap)
module TP = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition using (productMap)
open Products.Comparison W using (comparison)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

record FunctorComparison : Set l where
  field
    functor : (C D : S.CAT) → T.Equiv (W.cat (FS.Fun C D)) (FT.Fun (W.cat C) (W.cat D))
  arrow : (C D : S.CAT) → T.MAP (W.cat (FS.Fun C D)) (FT.Fun (W.cat C) (W.cat D))
  arrow C D = T.Equiv.functor (functor C D)
  field
    evaluation : (C D : S.CAT)
      → T._=₁_ (W.map (FS.funEval {C} {D}))
        (TC.funUncurry (arrow C D) ∘ comparison (FS.Fun C D) C)

module Consequences (K : FunctorComparison) where
  open FunctorComparison K

  uncurry : {X C D : S.CAT} (h : S.MAP X (FS.Fun C D))
    → T._=₁_ (W.map (SC.funUncurry h))
      (TC.funUncurry (arrow C D ∘ W.map h) ∘ comparison X C)
  uncurry {X} {C} {D} h = W.comp (SP.productMap h (S.id C)) FS.funEval then
    (evaluation C D ▷ W.map (SP.productMap h (S.id C))) then
    T.comp-assoc (W.map (SP.productMap h (S.id C))) (comparison (FS.Fun C D) C)
      (TC.funUncurry (arrow C D)) then
    (TC.funUncurry (arrow C D) ◁ ProductNaturality.Fixed.naturality W C h) then
    (T.comp-assoc (comparison X C) (TP.productMap (W.map h) (T.id (W.cat C)))
      (TC.funUncurry (arrow C D))) ⁻¹ then
    ((TC.funUncurry-restrict (arrow C D) (W.map h)) ⁻¹ ▷ comparison X C)

  module ProductsPreserved (WP : Products.PreservesProducts W) where
    inverse-product : (X C : S.CAT)
      → T.MAP (T._×_ (W.cat X) (W.cat C)) (W.cat (S._×_ X C))
    inverse-product X C = T.IsEquiv.inverse (Products.PreservesProducts.comparison-isEquiv WP X C)

    curry : {X C D : S.CAT} (f : S.MAP (S._×_ X C) D)
      → T._=₁_ (arrow C D ∘ W.map (SC.funCurry f))
        (TC.funCurry (W.map f ∘ inverse-product X C))
    curry {X} {C} {D} f = TC.funReflect _ _
      ((T.comp-unitʳ (TC.funUncurry (arrow C D ∘ W.map (SC.funCurry f)))) ⁻¹ then
        (TC.funUncurry (arrow C D ∘ W.map (SC.funCurry f)) ◁
          T.IsEquiv.retractionIso (Products.PreservesProducts.comparison-isEquiv WP X C)) then
        (T.comp-assoc (inverse-product X C) (comparison X C)
          (TC.funUncurry (arrow C D ∘ W.map (SC.funCurry f)))) ⁻¹ then
        ((uncurry (SC.funCurry f)) ⁻¹ ▷ inverse-product X C) then
        (W.term (SC.funCurry-β f) ▷ inverse-product X C) then
        (TC.funCurry-β (W.map f ∘ inverse-product X C)) ⁻¹)
```
