# Frobenius

The two extension rules give inverse functors between the sum of
`W C × B` and `C × Σ B`. The inverse is obtained by extending the pair
functor as a family with parameter `C`. The inverse equations are proved
by the corresponding reflection rules.

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
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumFamilies as Families
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestrictionPostcomposition as Postcomposition

module SCT.VolumeI.Chapter05.Section02.Frobenius
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (K : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (C : View.CAT S) (B : View.CAT T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module Q = Sums.DependentSums Q
module QA = SumAction W P Q using (reflect; flatten-post)
module Family (D : S.CAT) = Families W WP MS MT FS FT K P Q B D
  using (restrict; restrict-cong; extend; extend-β; reflect)
open Postcomposition W WP MS MT FS FT K P Q B using (restrict-post)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

LocalProduct : T.CAT
LocalProduct = T._×_ (W.cat C) B
TotalProduct : S.CAT
TotalProduct = S._×_ C (Q.Σ B)

inclusion : T.MAP LocalProduct (W.cat TotalProduct)
inclusion = Family.restrict TotalProduct (S.id TotalProduct)

F : S.MAP (Q.Σ LocalProduct) TotalProduct
F = Q.extend inclusion

G : S.MAP TotalProduct (Q.Σ LocalProduct)
G = Family.extend (Q.Σ LocalProduct) (Q.pair LocalProduct)

right-inverse : S._=₁_ (S._∘_ F G) (S.id TotalProduct)
right-inverse = Family.reflect TotalProduct
  (restrict-post F G then
    (W.map F ◁ Family.extend-β (Q.Σ LocalProduct) (Q.pair LocalProduct)) then
    (Q.extend-β inclusion) ⁻¹)

left-inverse : S._=₁_ (S._∘_ G F) (S.id (Q.Σ LocalProduct))
left-inverse = QA.reflect
  (QA.flatten-post G F then (W.map G ◁ (Q.extend-β inclusion) ⁻¹) then
    (restrict-post G (S.id TotalProduct)) ⁻¹ then
    Family.restrict-cong (Q.Σ LocalProduct) (S.comp-unitʳ G) then
    Family.extend-β (Q.Σ LocalProduct) (Q.pair LocalProduct) then
    (T.comp-unitˡ (Q.pair LocalProduct)) ⁻¹ then
    ((W.unit (Q.Σ LocalProduct)) ⁻¹ ▷ Q.pair LocalProduct))

comparison-isEquiv : S.IsEquiv F
comparison-isEquiv = record
  { inverse = G ; sectionIso = S._⁻¹ left-inverse ; retractionIso = S._⁻¹ right-inverse }

comparison : S.Equiv (Q.Σ LocalProduct) TotalProduct
comparison = record { functor = F ; isEquiv = comparison-isEquiv }
```
