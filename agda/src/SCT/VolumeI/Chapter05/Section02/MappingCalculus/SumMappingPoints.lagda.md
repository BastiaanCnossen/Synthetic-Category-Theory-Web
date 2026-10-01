# The sum mapping equivalence on named functors

The mapping-anima equivalence sends an absolute functor to the section
represented by its restriction along the pair functor. Consequently its
inverse sends a local functor to its specified extension.

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
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumMappingNaturality as Naturality
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestriction as Restriction
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestrictionPostcomposition as Post

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumMappingPoints
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
module P = Products.DependentProducts P
module Q = Sums.DependentSums Q
module SM = Setup S MS
  using (mapCurry-β; nameMap)
module TM = Setup T MT
  using (Map; mapCurry; mapCurry-cong; mapCurry-β; mapReflect; mapUncurry-restrict; nameMap; nameMapIso;
    productMap)
module PA = ProductAction W P using (reflect; curry-cong)
module M = SumMapping W WP MS MT FS FT K P Q B D
  using (forth; back; back-cong; back-forth; module Result)
module R (E : S.CAT) = Restriction W WP MS MT FS FT K P Q B E
  using (restrict; restrict-cong; χ; χ-equiv; χ⁻¹; insertion)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)
open Calculus S using () renaming (_then_ to _thenS_)

restrict-projection : {X : S.CAT}
  → T._=₁_ (R.restrict (Q.Σ B) (S.pr₂ {X} {Q.Σ B})) (Q.pair B ∘ T.pr₂)
restrict-projection {X} = (projection-inverse ▷ R.insertion (Q.Σ B) X) then
  T.pair-β₂ (T.id (W.cat X) ∘ T.pr₁) (Q.pair B ∘ T.pr₂)
  where
  χ = R.χ (Q.Σ B) X
  i = R.χ⁻¹ (Q.Σ B) X
  projection-inverse = ((T.pair-β₂ (W.map S.pr₁) (W.map S.pr₂)) ⁻¹ ▷ i) then
    T.comp-assoc i χ T.pr₂ then
    (T.pr₂ ◁ (T.IsEquiv.retractionIso (R.χ-equiv (Q.Σ B) X)) ⁻¹) then T.comp-unitʳ T.pr₂

restrict-constant : {X : S.CAT} (h : S.MAP (Q.Σ B) D)
  → T._=₁_ (R.restrict D (S._∘_ h (S.pr₂ {X}))) (Q.flatten h ∘ T.pr₂)
restrict-constant h = Post.restrict-post W WP MS MT FS FT K P Q B h S.pr₂ then
  (W.map h ◁ restrict-projection) then (T.comp-assoc T.pr₂ (Q.pair B) (W.map h)) ⁻¹

local-name : T.MAP B (W.cat D) → S.MAP S.One (P.Π (TM.Map B (W.cat D)))
local-name f = P.curry (TM.nameMap f ∘ T.terminate (W.cat S.One))

local-name-cong : {f g : T.MAP B (W.cat D)} → T._=₁_ f g → S._=₁_ (local-name f) (local-name g)
local-name-cong α = PA.curry-cong (TM.nameMapIso α ▷ T.terminate (W.cat S.One))

name-constant : (f : T.MAP B (W.cat D))
  → T._=₁_ (TM.mapCurry (W.anima S.one-isAn) (f ∘ T.pr₂))
      (TM.nameMap f ∘ T.terminate (W.cat S.One))
name-constant f = TM.mapReflect (W.anima S.one-isAn) _ _
  (TM.mapCurry-β (W.anima S.one-isAn) _ then
    (TM.mapUncurry-restrict (TM.nameMap f) (T.terminate (W.cat S.One)) then
      (TM.mapCurry-β T.one-isAn (f ∘ T.pr₂) ▷ TM.productMap (T.terminate (W.cat S.One)) (T.id B)) then
      T.comp-assoc (TM.productMap (T.terminate (W.cat S.One)) (T.id B)) T.pr₂ f then
      (f ◁ (T.pair-β₂ _ _ then T.comp-unitˡ T.pr₂))) ⁻¹)

forth-name : (h : S.MAP (Q.Σ B) D)
  → S._=₁_ (M.forth S.one-isAn (SM.nameMap h)) (local-name (Q.flatten h))
forth-name h = PA.curry-cong
  (TM.mapCurry-cong (W.anima S.one-isAn)
    (R.restrict-cong D (SM.mapCurry-β S.one-isAn (S._∘_ h S.pr₂)) then restrict-constant h) then
    name-constant (Q.flatten h))

back-name : (f : T.MAP B (W.cat D))
  → S._=₁_ (M.back S.one-isAn (local-name f)) (SM.nameMap (Q.extend f))
back-name f = M.back-cong S.one-isAn
    (local-name-cong (Q.extend-β f) thenS S._⁻¹ (forth-name (Q.extend f))) thenS
  M.back-forth S.one-isAn (SM.nameMap (Q.extend f))

comparison-name : (f : T.MAP B (W.cat D))
  → S._=₁_ (S._∘_ M.Result.G (local-name f)) (SM.nameMap (Q.extend f))
comparison-name f = Naturality.back-computation W WP MS MT FS FT K P Q B S.one-isAn (local-name f) thenS
  back-name f
```
