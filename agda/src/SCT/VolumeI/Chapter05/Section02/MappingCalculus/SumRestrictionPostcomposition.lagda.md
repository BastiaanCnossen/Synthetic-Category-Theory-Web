# Postcomposition and restriction of families

Restriction of a family commutes with an absolute functor in its target,
using the specified compositor of weakening.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestriction as Restriction

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestrictionPostcomposition
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (K : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (B : View.CAT T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module Q = Sums.DependentSums Q
module At (D : S.CAT) = Restriction W WP MS MT FS FT K P Q B D using (restrict; χ⁻¹; insertion)
open T using (_∘_; _◁_; _▷_)
open Calculus T using (_then_)

restrict-post : {R D E : S.CAT} (h : S.MAP D E) (f : S.MAP (S._×_ R (Q.Σ B)) D)
  → T._=₁_ (At.restrict E (S._∘_ h f)) (W.map h ∘ At.restrict D f)
restrict-post {R} {D} h f = ((W.comp f h ▷ At.χ⁻¹ D R) ▷ At.insertion D R) then
  (T.comp-assoc (At.χ⁻¹ D R) (W.map f) (W.map h) ▷ At.insertion D R) then
  T.comp-assoc (At.insertion D R) (W.map f ∘ At.χ⁻¹ D R) (W.map h)
```
