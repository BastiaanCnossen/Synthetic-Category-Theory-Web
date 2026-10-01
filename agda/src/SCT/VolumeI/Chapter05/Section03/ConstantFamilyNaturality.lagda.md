# Naturality of the total category of a constant family

The comparison with `A × C` is natural in `C`. Its first component uses
naturality of the total projection; its second uses the computation rule
for extending along the pair functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps

module SCT.VolumeI.Chapter05.Section03.ConstantFamilyNaturality
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A)) where

private
  module S = View S
  module T = View T
module W = Weakening W
module Q = Sums.DependentSums Q
module SumAction = Action W P Q using (Σ-map; counit; counit-natural)
module G = Point W P Q A e using (base; projection; projection-natural)
open S using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus S using (_then_; pair-pre; pair-cong)
open ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (productMap)

comparison : (C : S.CAT) → S.MAP (Q.Σ (W.cat C)) (S._×_ G.base C)
comparison C = S.pair (G.projection (W.cat C)) (SumAction.counit C)

naturality : {C D : S.CAT} (f : S.MAP C D)
  → S._=₁_ (comparison D ∘ SumAction.Σ-map (W.map f)) (productMap (S.id G.base) f ∘ comparison C)
naturality {C} {D} f = pair-pre (G.projection (W.cat D)) (SumAction.counit D) (SumAction.Σ-map (W.map f)) then
  pair-cong (G.projection-natural (W.map f)) (SumAction.counit-natural f) then
  (pair-pre (S.id G.base ∘ S.pr₁) (f ∘ S.pr₂) (comparison C) then
    pair-cong
      (S.comp-assoc (comparison C) S.pr₁ (S.id G.base) then
       (S.id G.base ◁ S.pair-β₁ (G.projection (W.cat C)) (SumAction.counit C)) then
       S.comp-unitˡ (G.projection (W.cat C)))
      (S.comp-assoc (comparison C) S.pr₂ f then
       (f ◁ S.pair-β₂ (G.projection (W.cat C)) (SumAction.counit C)))) ⁻¹
```
