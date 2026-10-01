# Weakening left uncurrying

The comparison is obtained from preservation of ordinary evaluation and
the comparison for product symmetry.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as Products
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ProductNaturality as ProductNaturality
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section07.Currying as Currying
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.LeftCurrying as Left

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.LeftCurryingPreservation
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (K : Preservation.FunctorComparison W MS MT FS FT) where

private
  module S = View S
  module T = View T
module W = Weakening W
module FS = Functors.FunctorCategories FS
module SC = Left S MS FS using (uncurry)
module TC = Left T MT FT using (uncurry)
module NativeT = Currying T MT FT using (funUncurry)
module SP = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (swap)
module TP = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition using (swap)
module K = Preservation.FunctorComparison K
open Products.Comparison W using (comparison)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

uncurry : {R B D : S.CAT} (h : S.MAP B (FS.Fun R D))
  → T._=₁_ (W.map (SC.uncurry h))
    (TC.uncurry (K.arrow R D ∘ W.map h) ∘ comparison R B)
uncurry {R} {B} {D} h = W.comp SP.swap _ then
  (Preservation.Consequences.uncurry W MS MT FS FT K h ▷ W.map SP.swap) then
  T.comp-assoc (W.map SP.swap) (comparison B R) (NativeT.funUncurry (K.arrow R D ∘ W.map h)) then
  (NativeT.funUncurry (K.arrow R D ∘ W.map h) ◁ ProductNaturality.swap W R B) then
  (T.comp-assoc (comparison R B) TP.swap (NativeT.funUncurry (K.arrow R D ∘ W.map h))) ⁻¹
```
