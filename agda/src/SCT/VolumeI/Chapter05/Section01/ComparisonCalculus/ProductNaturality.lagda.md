# Naturality of the product comparison

The canonical product comparison is natural in each input. The formula
below changes the first input and keeps the second fixed; it will be used
when changing the parameter of a curried functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as Products
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ProductNaturality
  {l : Level} {S T : Theory l l l} (W : Weakening S T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module SProduct = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition
module TProduct = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition
open Products.Comparison W using (comparison; pairing)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_; pair-pre; pair-cong)

module Fixed (X : S.CAT) where
  source : {R Q : S.CAT} (r : S.MAP R Q)
    → T.MAP (W.cat (S._×_ R X)) (T._×_ (W.cat Q) (W.cat X))
  source {R} {Q} r = comparison Q X ∘ W.map (SProduct.productMap r (S.id X))

  middle : {R Q : S.CAT} (r : S.MAP R Q)
    → T.MAP (W.cat (S._×_ R X)) (T._×_ (W.cat Q) (W.cat X))
  middle r = T.pair (W.map r ∘ W.map S.pr₁) (W.map S.pr₂)

  target : {R Q : S.CAT} (r : S.MAP R Q)
    → T.MAP (W.cat (S._×_ R X)) (T._×_ (W.cat Q) (W.cat X))
  target {R} r = TProduct.productMap (W.map r) (T.id (W.cat X)) ∘ comparison R X

  source-middle : {R Q : S.CAT} (r : S.MAP R Q) → T._=₁_ (source r) (middle r)
  source-middle r = pairing (S._∘_ r S.pr₁) (S._∘_ (S.id X) S.pr₂) then
    pair-cong (W.comp S.pr₁ r) (W.term (S.comp-unitˡ S.pr₂))

  target-middle : {R Q : S.CAT} (r : S.MAP R Q) → T._=₁_ (target r) (middle r)
  target-middle {R} r = pair-pre (W.map r ∘ T.pr₁) (T.id (W.cat X) ∘ T.pr₂) (comparison R X) then
    pair-cong
      (T.comp-assoc (comparison R X) T.pr₁ (W.map r) then
        (W.map r ◁ T.pair-β₁ (W.map S.pr₁) (W.map S.pr₂)))
      (T.comp-assoc (comparison R X) T.pr₂ (T.id (W.cat X)) then
        T.comp-unitˡ (T.pr₂ ∘ comparison R X) then T.pair-β₂ (W.map S.pr₁) (W.map S.pr₂))

  naturality : {R Q : S.CAT} (r : S.MAP R Q) → T._=₁_ (source r) (target r)
  naturality r = source-middle r then (target-middle r) ⁻¹

module Inverse (P : Products.PreservesProducts W) where
  inverse : (R X : S.CAT) → T.MAP (T._×_ (W.cat R) (W.cat X)) (W.cat (S._×_ R X))
  inverse R X = T.IsEquiv.inverse (Products.PreservesProducts.comparison-isEquiv P R X)

  naturality : {R Q : S.CAT} (X : S.CAT) (r : S.MAP R Q)
    → T._=₁_ (W.map (SProduct.productMap r (S.id X)) ∘ inverse R X)
      (inverse Q X ∘ TProduct.productMap (W.map r) (T.id (W.cat X)))
  naturality {R} {Q} X r = T.equiv-reflect
    (Products.PreservesProducts.comparison-isEquiv P Q X) _ _
    ((T.comp-assoc (inverse R X) (W.map (SProduct.productMap r (S.id X))) (comparison Q X)) ⁻¹ then
      (Fixed.naturality X r ▷ inverse R X) then
      T.comp-assoc (inverse R X) (comparison R X) k then
      (k ◁ (T.IsEquiv.retractionIso (Products.PreservesProducts.comparison-isEquiv P R X)) ⁻¹) then
      T.comp-unitʳ k then
      (T.comp-unitˡ k) ⁻¹ then
      (T.IsEquiv.retractionIso (Products.PreservesProducts.comparison-isEquiv P Q X) ▷ k) then
      T.comp-assoc k (inverse Q X) (comparison Q X))
    where
    k = TProduct.productMap (W.map r) (T.id (W.cat X))

swap : (C D : S.CAT)
  → T._=₁_ (comparison D C ∘ W.map (SProduct.swap {C} {D}))
    (TProduct.swap ∘ comparison C D)
swap C D = pairing S.pr₂ S.pr₁ then
  (pair-pre T.pr₂ T.pr₁ (comparison C D) then
    pair-cong (T.pair-β₂ (W.map S.pr₁) (W.map S.pr₂))
      (T.pair-β₁ (W.map S.pr₁) (W.map S.pr₂))) ⁻¹
```
