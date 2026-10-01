# Naturality of the sum mapping equivalence

Extension of families commutes with postcomposition. This gives the
naturality square for the inverse of the mapping-anima equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as ProductAction
import SCT.VolumeI.Chapter05.Section02.SumMapping as SumMapping
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumFamilies as Families
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestrictionPostcomposition as Restriction

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumMappingNaturality
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
module P = Products.DependentProducts P
module Q = Sums.DependentSums Q
module SM = Setup S MS
  using (mapCurry-β; mapPost; mapPost-uncurry; mapReflect)
module TM = Setup T MT
  using (map-isAn; mapPost; mapPost-uncurry; mapUncurry; mapUncurry-cong)
module PA = ProductAction W P using (Π-map; Π-map-β; uncurry-pre)
module Family (D : S.CAT) = Families W WP MS MT FS FT K P Q B D
  using (extend; extend-β; extend-η; extend-cong; restrict; reflect)
module MappingAt (D : S.CAT) = SumMapping W WP MS MT FS FT K P Q B D
  using (back; back-cong; back-pre; Right; module Result)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)
open Calculus S using () renaming (_then_ to _thenS_)

extend-post : {R D E : S.CAT} (f : S.MAP D E)
  (h : T.MAP (T._×_ (W.cat R) B) (W.cat D))
  → S._=₁_ (Family.extend E (W.map f ∘ h)) (S._∘_ f (Family.extend D h))
extend-post {D = D} {E} f h = Family.reflect E
  (Family.extend-β E (W.map f ∘ h) then
    (W.map f ◁ (Family.extend-β D h) ⁻¹) then
    (Restriction.restrict-post W WP MS MT FS FT K P Q B f (Family.extend D h)) ⁻¹)

uncurry-post : {X : S.CAT} {D E : T.CAT} (f : T.MAP D E) (h : S.MAP X (P.Π D))
  → T._=₁_ (P.uncurry (S._∘_ (PA.Π-map f) h)) (f ∘ P.uncurry h)
uncurry-post {D = D} f h = PA.uncurry-pre (PA.Π-map f) h then
  ((PA.Π-map-β f) ⁻¹ ▷ W.map h) then T.comp-assoc (W.map h) (P.evaluation D) f

back-natural : {R D E : S.CAT} (rAn : S.isAn R) (f : S.MAP D E)
  (h : S.MAP R (MappingAt.Right D))
  → S._=₁_ (MappingAt.back E rAn (S._∘_ (PA.Π-map (TM.mapPost (W.map f))) h))
      (S._∘_ (SM.mapPost f) (MappingAt.back D rAn h))
back-natural {D = D} {E} rAn f h = SM.mapReflect rAn _ _
  (SM.mapCurry-β rAn _ thenS
    Family.extend-cong E (TM.mapUncurry-cong (uncurry-post (TM.mapPost (W.map f)) h) then
      TM.mapPost-uncurry (W.map f) (P.uncurry h)) thenS
    extend-post f (TM.mapUncurry (P.uncurry h)) thenS
    S._⁻¹ (S._∙_ (S._◁_ f (SM.mapCurry-β rAn _))
      (SM.mapPost-uncurry f (MappingAt.back D rAn h))))

back-computation : {R D : S.CAT} (rAn : S.isAn R) (h : S.MAP R (MappingAt.Right D))
  → S._=₁_ (S._∘_ (MappingAt.Result.G D) h) (MappingAt.back D rAn h)
back-computation {D = D} rAn h = S._⁻¹ (MappingAt.back-pre D rAn
    (P.Π-isAn (TM.map-isAn B (W.cat D))) (S.id (MappingAt.Right D)) h) thenS
  MappingAt.back-cong D rAn (S.comp-unitˡ h)

comparison : {D E : S.CAT} (f : S.MAP D E)
  → S._=₁_ (S._∘_ (MappingAt.Result.G E) (PA.Π-map (TM.mapPost (W.map f))))
      (S._∘_ (SM.mapPost f) (MappingAt.Result.G D))
comparison {D} {E} f = back-computation (P.Π-isAn (TM.map-isAn B (W.cat D))) _ thenS
  MappingAt.back-cong E (P.Π-isAn (TM.map-isAn B (W.cat D)))
    (S._⁻¹ (S.comp-unitʳ (PA.Π-map (TM.mapPost (W.map f))))) thenS
  back-natural (P.Π-isAn (TM.map-isAn B (W.cat D))) f (S.id (MappingAt.Right D))
```
