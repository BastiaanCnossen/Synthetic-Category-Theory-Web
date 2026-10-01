# The specified Frobenius comparison

The equivalence constructed by extending families agrees with the pair
of extension of the first projection and the sum of the second projection.
The final comparison uses the order of factors in the manuscript.

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
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumRestriction as Restriction
import SCT.VolumeI.Chapter05.Section02.Frobenius as Frobenius

module SCT.VolumeI.Chapter05.Section02.FrobeniusComparison
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
module QA = SumAction W P Q using (reflect; Σ-map; Σ-map-β; Σ-map-comp; Σ-map-cong; extend-cong; extend-local-pre)
module E = Equivalences.SumResults W P Q using (Σ-map-isEquiv)
module F = Frobenius W WP MS MT FS FT K P Q C B
  using (LocalProduct; TotalProduct; inclusion; F; comparison-isEquiv)
module R = Restriction W WP MS MT FS FT K P Q B F.TotalProduct using (χ; χ⁻¹; χ-equiv; insertion)
module SP = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (swap; swap-isEquiv)
module TP = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition using (swap; swap-isEquiv)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_; pair-cong; pair-pre)
module SC = Calculus S using (pair-cong; pair-pre)
open Calculus S using () renaming (_then_ to _thenS_)

left-comparison : S.MAP (Q.Σ F.LocalProduct) F.TotalProduct
left-comparison = S.pair (Q.extend T.pr₁) (QA.Σ-map T.pr₂)

middle : T.MAP F.LocalProduct (T._×_ (W.cat C) (W.cat (Q.Σ B)))
middle = T.pair T.pr₁ (Q.pair B ∘ T.pr₂)

constructed-image : T._=₁_ (R.χ C ∘ Q.flatten F.F) middle
constructed-image = (R.χ C ◁ (Q.extend-β F.inclusion) ⁻¹) then
  (T.comp-assoc (R.insertion C) (W.map (S.id F.TotalProduct) ∘ R.χ⁻¹ C) (R.χ C)) ⁻¹ then
  ((R.χ C ◁ ((W.unit F.TotalProduct ▷ R.χ⁻¹ C) then T.comp-unitˡ (R.χ⁻¹ C))) ▷ R.insertion C) then
  ((T.IsEquiv.retractionIso (R.χ-equiv C)) ⁻¹ ▷ R.insertion C) then
  T.comp-unitˡ (R.insertion C) then pair-cong (T.comp-unitˡ T.pr₁) (T.idIso _)

specified-image : T._=₁_ (R.χ C ∘ Q.flatten left-comparison) middle
specified-image = (T.comp-assoc (Q.pair F.LocalProduct) (W.map left-comparison) (R.χ C)) ⁻¹ then
  (WeakProducts.Comparison.pairing W (Q.extend T.pr₁) (QA.Σ-map T.pr₂) ▷ Q.pair F.LocalProduct) then
  pair-pre (W.map (Q.extend T.pr₁)) (W.map (QA.Σ-map T.pr₂)) (Q.pair F.LocalProduct) then
  pair-cong ((Q.extend-β T.pr₁) ⁻¹) ((QA.Σ-map-β T.pr₂) ⁻¹)

agrees : S._=₁_ F.F left-comparison
agrees = QA.reflect (T.equiv-reflect (R.χ-equiv C) _ _ (constructed-image then specified-image ⁻¹))

left-isEquiv : S.IsEquiv left-comparison
left-isEquiv = S.equiv-transport agrees F.comparison-isEquiv

comparison : S.MAP (Q.Σ (T._×_ B (W.cat C))) (S._×_ (Q.Σ B) C)
comparison = S.pair (QA.Σ-map T.pr₁) (Q.extend T.pr₂)

swapped : S.MAP (Q.Σ (T._×_ B (W.cat C))) (S._×_ (Q.Σ B) C)
swapped = S._∘_ SP.swap (S._∘_ left-comparison (QA.Σ-map TP.swap))

swapped-isEquiv : S.IsEquiv swapped
swapped-isEquiv = S.equiv-compose _ SP.swap
  (S.equiv-compose _ left-comparison (E.Σ-map-isEquiv (TP.swap-isEquiv B (W.cat C))) left-isEquiv)
  (SP.swap-isEquiv C (Q.Σ B))

swapped-agrees : S._=₁_ swapped comparison
swapped-agrees = SC.pair-pre S.pr₂ S.pr₁ (S._∘_ left-comparison (QA.Σ-map TP.swap)) thenS
  SC.pair-cong
    (S._⁻¹ (S.comp-assoc (QA.Σ-map TP.swap) left-comparison S.pr₂) thenS
      S._▷_ (S.pair-β₂ (Q.extend T.pr₁) (QA.Σ-map T.pr₂)) (QA.Σ-map TP.swap) thenS
      S._⁻¹ (QA.Σ-map-comp TP.swap T.pr₂) thenS QA.Σ-map-cong (T.pair-β₂ T.pr₂ T.pr₁))
    (S._⁻¹ (S.comp-assoc (QA.Σ-map TP.swap) left-comparison S.pr₁) thenS
      S._▷_ (S.pair-β₁ (Q.extend T.pr₁) (QA.Σ-map T.pr₂)) (QA.Σ-map TP.swap) thenS
      QA.extend-local-pre T.pr₁ TP.swap thenS QA.extend-cong (T.pair-β₁ T.pr₂ T.pr₁))

comparison-isEquiv : S.IsEquiv comparison
comparison-isEquiv = S.equiv-transport swapped-agrees swapped-isEquiv
```
