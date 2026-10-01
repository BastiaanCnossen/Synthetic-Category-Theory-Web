# Total categories of constant families

The first projection and the sum counit give the specified equivalence
`Σ (W C) → A × C`. We compare it with Frobenius for the local terminal
category, retaining both components of the comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus as ProductEquivalences
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section02.FrobeniusComparison as Frobenius
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point

module SCT.VolumeI.Chapter05.Section03.ConstantFamilies
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (K : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (C : View.CAT S) where

private
  module S = View S
  module T = View T
module W = Weakening W
module Q = Sums.DependentSums Q
module QA = SumAction W P Q using (Σ-map; Σ-map-cong; counit; extend-local-pre; extend-cong)
module E = Equivalences.SumResults W P Q using (Σ-map-isEquiv)
module G = Point W P Q A e using (base; projection; projection-natural)
module F = Frobenius W WP MS MT FS FT K P Q C T.One using (comparison; comparison-isEquiv)
module SP = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (productMap)
module TP = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition using (swap; swap-isEquiv; product-unitʳ-isEquiv)
open S using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus S using (_then_; pair-cong; pair-pre)

comparison : S.MAP (Q.Σ (W.cat C)) (S._×_ G.base C)
comparison = S.pair (G.projection (W.cat C)) (QA.counit C)

local-unit : T.IsEquiv (T.pr₂ {T.One} {W.cat C})
local-unit = T.equiv-transport (T.pair-β₁ T.pr₂ T.pr₁)
  (T.equiv-compose TP.swap T.pr₁ (TP.swap-isEquiv T.One (W.cat C)) (TP.product-unitʳ-isEquiv (W.cat C)))

unit-map : S.MAP (Q.Σ (T._×_ T.One (W.cat C))) (Q.Σ (W.cat C))
unit-map = QA.Σ-map T.pr₂

change-base : S.MAP (S._×_ (Q.Σ T.One) C) (S._×_ G.base C)
change-base = SP.productMap (S.Equiv.functor e) (S.id C)

middle : S.MAP (Q.Σ (T._×_ T.One (W.cat C))) (S._×_ G.base C)
middle = S.pair (S.Equiv.functor e ∘ QA.Σ-map T.pr₁) (Q.extend T.pr₂)

comparison-image : S._=₁_ (comparison ∘ unit-map) middle
comparison-image = pair-pre (G.projection (W.cat C)) (QA.counit C) unit-map then
  pair-cong
    (G.projection-natural T.pr₂ then (S.Equiv.functor e ◁ QA.Σ-map-cong (T.terminal-iso _ _)))
    (QA.extend-local-pre (T.id (W.cat C)) T.pr₂ then QA.extend-cong (T.comp-unitˡ T.pr₂))

frobenius-image : S._=₁_ (change-base ∘ F.comparison) middle
frobenius-image = pair-pre (S.Equiv.functor e ∘ S.pr₁) (S.id C ∘ S.pr₂) F.comparison then
  pair-cong
    (S.comp-assoc F.comparison S.pr₁ (S.Equiv.functor e) then
      (S.Equiv.functor e ◁ S.pair-β₁ (QA.Σ-map T.pr₁) (Q.extend T.pr₂)))
    (S.comp-assoc F.comparison S.pr₂ (S.id C) then S.comp-unitˡ _ then
      S.pair-β₂ (QA.Σ-map T.pr₁) (Q.extend T.pr₂))

comparison-isEquiv : S.IsEquiv comparison
comparison-isEquiv = S.equiv-cancel-right unit-map comparison (E.Σ-map-isEquiv local-unit)
  (S.equiv-transport (frobenius-image then comparison-image ⁻¹)
    (S.equiv-compose F.comparison change-base F.comparison-isEquiv
      (ProductEquivalences.productMap-isEquiv S (S.Equiv.functor e) (S.id C)
        (S.Equiv.isEquiv e) (S.id-isEquiv C))))

over-base : S._=₁_ (S.pr₁ ∘ comparison) (G.projection (W.cat C))
over-base = S.pair-β₁ (G.projection (W.cat C)) (QA.counit C)
```
