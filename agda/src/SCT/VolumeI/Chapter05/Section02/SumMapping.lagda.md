# Mapping out of a dependent sum

Restriction along the pair functor induces
`Map (Σ B) D ≃ Π (Map B (W D))`. Its inverse is the extension of
families constructed using preservation of functor categories. All
calculations are made with arbitrary anima parameters before applying
the criterion comparing represented families.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as MapCurrying
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as ProductAction
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumFamilies as Families
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.Representations as Representations

module SCT.VolumeI.Chapter05.Section02.SumMapping
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
module MS = Mapping.MappingAnimae MS
module MT = Mapping.MappingAnimae MT
module P = Products.DependentProducts P
module Q = Sums.DependentSums Q
module PA = ProductAction W P using (reflect; curry-cong; uncurry-pre)
module SC = MapCurrying S MS using (mapUncurry-cong; mapUncurry-restrict; mapCurry-cong; mapReflect)
module TC = MapCurrying T MT using (mapUncurry-cong; mapUncurry-restrict; mapCurry-cong; mapReflect)
module SP = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (productMap)
module TP = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition using (productMap)
module Family = Families W WP MS MT FS FT K P Q B D
  using (restrict; restrict-cong; extend; extend-β; extend-η; extend-cong; extend-pre)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)
open Calculus S using () renaming (_then_ to _thenS_)

Left : S.CAT
Left = MS.Map (Q.Σ B) D
LocalRight : T.CAT
LocalRight = MT.Map B (W.cat D)
Right : S.CAT
Right = P.Π LocalRight

forth : {R : S.CAT} → S.isAn R → S.MAP R Left → S.MAP R Right
forth rAn h = P.curry (MT.mapCurry (W.anima rAn) (Family.restrict (MS.mapUncurry h)))

back : {R : S.CAT} → S.isAn R → S.MAP R Right → S.MAP R Left
back rAn h = MS.mapCurry rAn (Family.extend (MT.mapUncurry (P.uncurry h)))

forth-cong : {R : S.CAT} (rAn : S.isAn R) {f g : S.MAP R Left}
  → S._=₁_ f g → S._=₁_ (forth rAn f) (forth rAn g)
forth-cong rAn α = PA.curry-cong (TC.mapCurry-cong (W.anima rAn)
  (Family.restrict-cong (SC.mapUncurry-cong α)))

back-cong : {R : S.CAT} (rAn : S.isAn R) {f g : S.MAP R Right}
  → S._=₁_ f g → S._=₁_ (back rAn f) (back rAn g)
back-cong rAn α = SC.mapCurry-cong rAn (Family.extend-cong
  (TC.mapUncurry-cong (P.evaluation LocalRight ◁ W.term α)))

back-forth : {R : S.CAT} (rAn : S.isAn R) (h : S.MAP R Left)
  → S._=₁_ (back rAn (forth rAn h)) h
back-forth rAn h = SC.mapReflect rAn _ _
  (MS.mapCurry-β rAn (Family.extend (MT.mapUncurry (P.uncurry (forth rAn h)))) thenS
    Family.extend-cong
      (TC.mapUncurry-cong ((P.curry-β (MT.mapCurry (W.anima rAn) (Family.restrict (MS.mapUncurry h)))) ⁻¹) then
        MT.mapCurry-β (W.anima rAn) (Family.restrict (MS.mapUncurry h))) thenS
    Family.extend-η (MS.mapUncurry h))

forth-back : {R : S.CAT} (rAn : S.isAn R) (h : S.MAP R Right)
  → S._=₁_ (forth rAn (back rAn h)) h
forth-back rAn h = PA.reflect
  ((P.curry-β (MT.mapCurry (W.anima rAn) (Family.restrict (MS.mapUncurry (back rAn h))))) ⁻¹ then
    TC.mapReflect (W.anima rAn) _ _
      (MT.mapCurry-β (W.anima rAn) (Family.restrict (MS.mapUncurry (back rAn h))) then
        Family.restrict-cong (MS.mapCurry-β rAn (Family.extend (MT.mapUncurry (P.uncurry h)))) then
        Family.extend-β (MT.mapUncurry (P.uncurry h))))

back-pre : {R H : S.CAT} (rAn : S.isAn R) (hAn : S.isAn H)
  (h : S.MAP H Right) (r : S.MAP R H)
  → S._=₁_ (back rAn (S._∘_ h r)) (S._∘_ (back hAn h) r)
back-pre rAn hAn h r = SC.mapReflect rAn _ _
  (MS.mapCurry-β rAn (Family.extend (MT.mapUncurry (P.uncurry (S._∘_ h r)))) thenS
    Family.extend-cong
      (TC.mapUncurry-cong (PA.uncurry-pre h r) then TC.mapUncurry-restrict (P.uncurry h) (W.map r)) thenS
    Family.extend-pre (MT.mapUncurry (P.uncurry h)) r thenS
    S._▷_ (S._⁻¹ (MS.mapCurry-β hAn (Family.extend (MT.mapUncurry (P.uncurry h)))))
      (SP.productMap r (S.id (Q.Σ B))) thenS
    S._⁻¹ (SC.mapUncurry-restrict (back hAn h) r))

module Result = Representations.Compare S Left Right (MS.map-isAn (Q.Σ B) D)
  (P.Π-isAn (MT.map-isAn B (W.cat D))) forth back forth-cong back-cong back-forth forth-back back-pre
  using (F; G; isEquiv; equivalence)

comparison : S.Equiv Left Right
comparison = Result.equivalence
```
