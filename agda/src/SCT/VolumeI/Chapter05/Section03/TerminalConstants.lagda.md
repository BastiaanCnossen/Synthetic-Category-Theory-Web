# Constant families in the terminal context

The counit `Σ W C → C` is an equivalence when the indexing anima is
terminal. Together with `TerminalContext.local-equivalence`, this gives
both category comparisons between the two theories. The comparison is
the counit itself, so its naturality is the already proved counit law.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section03.ConstantFamilies as Constants

module SCT.VolumeI.Chapter05.Section03.TerminalConstants
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (K : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.One S)) where

private
  module S = View S
  A : S.AN
  A = record { category = S.One ; witness = S.one-isAn }
module W = Weakening W
module Q = Sums.DependentSums Q
module QA = SumAction W P Q using (counit; counit-natural)
module Constant (C : S.CAT) = Constants W WP MS MT FS FT K P Q A e C
  using (comparison; comparison-isEquiv)
open ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition
  using (swap; swap-isEquiv; product-unitʳ-isEquiv)

second-isEquiv : (C : S.CAT) → S.IsEquiv (S.pr₂ {S.One} {C})
second-isEquiv C = S.equiv-transport (S.pair-β₁ S.pr₂ S.pr₁)
  (S.equiv-compose swap S.pr₁ (swap-isEquiv S.One C) (product-unitʳ-isEquiv C))

counit-isEquiv : (C : S.CAT) → S.IsEquiv (QA.counit C)
counit-isEquiv C = S.equiv-transport (S.pair-β₂ _ (QA.counit C))
  (S.equiv-compose (Constant.comparison C) S.pr₂ (Constant.comparison-isEquiv C) (second-isEquiv C))

equivalence : (C : S.CAT) → S.Equiv (Q.Σ (W.cat C)) C
equivalence C = record { functor = QA.counit C ; isEquiv = counit-isEquiv C }
```
