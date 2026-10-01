# Restricting a family along the pair functor

A family on the total category restricts to a local family by weakening
and the pair functor. This restriction commutes with parameter change.
Under left currying it is the ordinary flattening operation, followed by
the functor-category comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ProductNaturality as Naturality
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.LeftCurrying as Left
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.LeftCurryingPreservation as LeftPreservation
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.ProductSymmetry as Symmetry

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestriction
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (K : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (B : View.CAT T) (D : View.CAT S) where

private
  module S = View S
  module T = View T
module W = Weakening W
module FS = Functors.FunctorCategories FS
module Q = Sums.DependentSums Q
module K = Preservation.FunctorComparison K
module SC = Left S MS FS using (uncurry)
module TC = Left T MT FT using (uncurry; uncurry-cong; uncurry-pre)
module SP = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (productMap)
module TP = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition using (productMap)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

χ : (R : S.CAT) → T.MAP (W.cat (S._×_ R (Q.Σ B))) (T._×_ (W.cat R) (W.cat (Q.Σ B)))
χ R = WeakProducts.Comparison.comparison W R (Q.Σ B)
χ-equiv : (R : S.CAT) → T.IsEquiv (χ R)
χ-equiv R = WeakProducts.PreservesProducts.comparison-isEquiv WP R (Q.Σ B)
χ⁻¹ : (R : S.CAT) → T.MAP (T._×_ (W.cat R) (W.cat (Q.Σ B))) (W.cat (S._×_ R (Q.Σ B)))
χ⁻¹ R = T.IsEquiv.inverse (χ-equiv R)

insertion : (R : S.CAT) → T.MAP (T._×_ (W.cat R) B) (T._×_ (W.cat R) (W.cat (Q.Σ B)))
insertion R = TP.productMap (T.id (W.cat R)) (Q.pair B)

restrict : {R : S.CAT} → S.MAP (S._×_ R (Q.Σ B)) D → T.MAP (T._×_ (W.cat R) B) (W.cat D)
restrict {R} h = (W.map h ∘ χ⁻¹ R) ∘ insertion R

restrict-cong : {R : S.CAT} {f g : S.MAP (S._×_ R (Q.Σ B)) D}
  → S._=₁_ f g → T._=₁_ (restrict f) (restrict g)
restrict-cong {R} α = (W.term α ▷ χ⁻¹ R) ▷ insertion R

restrict-transpose : {R : S.CAT} (h : S.MAP (Q.Σ B) (FS.Fun R D))
  → T._=₁_ (restrict (SC.uncurry h)) (TC.uncurry (K.arrow R D ∘ Q.flatten h))
restrict-transpose {R} h =
  ((LeftPreservation.uncurry W MS MT FS FT K h ▷ χ⁻¹ R) ▷ insertion R) then
  ((T.comp-assoc (χ⁻¹ R) (χ R) (TC.uncurry (K.arrow R D ∘ W.map h))) ▷ insertion R) then
  ((TC.uncurry (K.arrow R D ∘ W.map h) ◁ (T.IsEquiv.retractionIso (χ-equiv R)) ⁻¹) ▷ insertion R) then
  (T.comp-unitʳ (TC.uncurry (K.arrow R D ∘ W.map h)) ▷ insertion R) then
  (TC.uncurry-pre (K.arrow R D ∘ W.map h) (Q.pair B)) ⁻¹ then
  TC.uncurry-cong (T.comp-assoc (Q.pair B) (W.map h) (K.arrow R D))

restrict-pre : {R H : S.CAT} (f : S.MAP (S._×_ H (Q.Σ B)) D) (r : S.MAP R H)
  → T._=₁_ (restrict (S._∘_ f (SP.productMap r (S.id (Q.Σ B)))))
    (restrict f ∘ TP.productMap (W.map r) (T.id B))
restrict-pre {R} {H} f r = ((W.comp (SP.productMap r (S.id (Q.Σ B))) f ▷ χ⁻¹ R) ▷ insertion R) then
  (T.comp-assoc (χ⁻¹ R) (W.map (SP.productMap r (S.id (Q.Σ B)))) (W.map f) ▷ insertion R) then
  ((W.map f ◁ Naturality.Inverse.naturality W WP (Q.Σ B) r) ▷ insertion R) then
  ((T.comp-assoc (TP.productMap (W.map r) (T.id (W.cat (Q.Σ B)))) (χ⁻¹ H) (W.map f)) ⁻¹ ▷ insertion R) then
  T.comp-assoc (insertion R) (TP.productMap (W.map r) (T.id (W.cat (Q.Σ B)))) (W.map f ∘ χ⁻¹ H) then
  ((W.map f ∘ χ⁻¹ H) ◁ Symmetry.independent T (W.map r) (Q.pair B)) then
  (T.comp-assoc (TP.productMap (W.map r) (T.id B)) (insertion H) (W.map f ∘ χ⁻¹ H)) ⁻¹
```
