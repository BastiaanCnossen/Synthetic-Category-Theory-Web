# Extending a family over a dependent sum

A local functor `W R × B → W D` extends to `R × Σ B → D`.
The construction curries in `W R`, uses the functor-category comparison,
and applies the sum extension rule. It does not use Frobenius. The
computation and uniqueness proofs also give compatibility with changes
of the parameter `R`.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestriction as Restriction
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.LeftCurrying as Left

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumFamilies
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
module Q = Sums.DependentSums Q
module K = Preservation.FunctorComparison K
module QA = SumAction W P Q using (reflect; extend-cong)
module SC = Left S MS FS using (uncurry; curry; curry-β; uncurry-cong)
module TC = Left T MT FT using (uncurry; curry; curry-β; curry-cong; uncurry-cong; reflect)
module SP = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (productMap)
module TP = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition using (productMap)
open Restriction W WP MS MT FS FT K P Q B D public
  using (restrict; restrict-cong; restrict-transpose; restrict-pre)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

inverse : (R : S.CAT) → T.MAP _ _
inverse R = T.IsEquiv.inverse (T.Equiv.isEquiv (K.functor R D))

extend : {R : S.CAT} → T.MAP (T._×_ (W.cat R) B) (W.cat D)
  → S.MAP (S._×_ R (Q.Σ B)) D
extend {R} f = SC.uncurry (Q.extend (inverse R ∘ TC.curry f))

extend-β : {R : S.CAT} (f : T.MAP (T._×_ (W.cat R) B) (W.cat D))
  → T._=₁_ (restrict (extend f)) f
extend-β {R} f = restrict-transpose (Q.extend (inverse R ∘ TC.curry f)) then
  TC.uncurry-cong ((K.arrow R D ◁ (Q.extend-β (inverse R ∘ TC.curry f)) ⁻¹) then
    (T.comp-assoc (TC.curry f) (inverse R) (K.arrow R D)) ⁻¹ then
    ((T.IsEquiv.retractionIso (T.Equiv.isEquiv (K.functor R D))) ⁻¹ ▷ TC.curry f) then
    T.comp-unitˡ (TC.curry f)) then TC.curry-β f

extend-cong : {R : S.CAT} {f g : T.MAP (T._×_ (W.cat R) B) (W.cat D)}
  → T._=₁_ f g → S._=₁_ (extend f) (extend g)
extend-cong {R} α = SC.uncurry-cong (QA.extend-cong (inverse R ◁ TC.curry-cong α))

reflect : {R : S.CAT} {f g : S.MAP (S._×_ R (Q.Σ B)) D}
  → T._=₁_ (restrict f) (restrict g) → S._=₁_ f g
reflect {R} {f} {g} α = S._∙_ (SC.curry-β g)
  (S._∙_ (SC.uncurry-cong (QA.reflect (T.equiv-reflect (T.Equiv.isEquiv (K.functor R D)) _ _
    (TC.reflect ((restrict-transpose (SC.curry f)) ⁻¹ then
      restrict-cong (SC.curry-β f) then α then
      (restrict-cong (SC.curry-β g)) ⁻¹ then restrict-transpose (SC.curry g))))))
    (S._⁻¹ (SC.curry-β f)))

extend-η : {R : S.CAT} (f : S.MAP (S._×_ R (Q.Σ B)) D)
  → S._=₁_ (extend (restrict f)) f
extend-η f = reflect (extend-β (restrict f))

extend-pre : {R H : S.CAT} (f : T.MAP (T._×_ (W.cat H) B) (W.cat D)) (r : S.MAP R H)
  → S._=₁_ (extend (f ∘ TP.productMap (W.map r) (T.id B)))
    (S._∘_ (extend f) (SP.productMap r (S.id (Q.Σ B))))
extend-pre f r = reflect (extend-β (f ∘ TP.productMap (W.map r) (T.id B)) then
  ((extend-β f) ⁻¹ ▷ TP.productMap (W.map r) (T.id B)) then (restrict-pre (extend f) r) ⁻¹)
```
