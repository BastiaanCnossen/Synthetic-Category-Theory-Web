# Mapping into a dependent product

Evaluation induces the equivalence
`Map X (Π B) ≃ Π (Map (W X) B)` of whole absolute animae.
The two transformations are first constructed for an arbitrary anima
parameter. Their inverse laws use both currying rules and the product
comparison. Naturality of the reverse transformation then identifies
these transformations with an actual equivalence of the represented animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ProductNaturality as Naturality
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as MapCurrying
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as ProductAction
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.Representations as Representations

module SCT.VolumeI.Chapter05.Section02.ProductMapping
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (P : Products.DependentProducts W) (X : View.CAT S) (B : View.CAT T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module MS = Mapping.MappingAnimae MS
module MT = Mapping.MappingAnimae MT
module P = Products.DependentProducts P
module PA = ProductAction W P using (reflect; curry-cong; curry-pre; uncurry-pre)
module SC = MapCurrying S MS using (mapUncurry-cong; mapUncurry-restrict; mapReflect)
module TC = MapCurrying T MT using (mapUncurry-cong; mapUncurry-restrict; mapCurry-cong; mapReflect)
module SP = ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (productMap)
module TP = ProductMaps T.vocabulary T.terminal T.products T.productLaws T.composition using (productMap)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

χ : (R : S.CAT) → T.MAP (W.cat (S._×_ R X)) (T._×_ (W.cat R) (W.cat X))
χ R = WeakProducts.Comparison.comparison W R X
χ-equiv : (R : S.CAT) → T.IsEquiv (χ R)
χ-equiv R = WeakProducts.PreservesProducts.comparison-isEquiv WP R X
χ⁻¹ : (R : S.CAT) → T.MAP (T._×_ (W.cat R) (W.cat X)) (W.cat (S._×_ R X))
χ⁻¹ R = T.IsEquiv.inverse (χ-equiv R)

Left : S.CAT
Left = MS.Map X (P.Π B)
LocalRight : T.CAT
LocalRight = MT.Map (W.cat X) B
Right : S.CAT
Right = P.Π LocalRight

left-evaluation : {R : S.CAT} → S.MAP R Left → T.MAP (T._×_ (W.cat R) (W.cat X)) B
left-evaluation {R} h = P.uncurry (MS.mapUncurry h) ∘ χ⁻¹ R

right-evaluation : {R : S.CAT} → S.MAP R Right → T.MAP (W.cat (S._×_ R X)) B
right-evaluation {R} h = MT.mapUncurry (P.uncurry h) ∘ χ R

forth : {R : S.CAT} → S.isAn R → S.MAP R Left → S.MAP R Right
forth rAn h = P.curry (MT.mapCurry (W.anima rAn) (left-evaluation h))

back : {R : S.CAT} → S.isAn R → S.MAP R Right → S.MAP R Left
back rAn h = MS.mapCurry rAn (P.curry (right-evaluation h))

forth-cong : {R : S.CAT} (rAn : S.isAn R) {f g : S.MAP R Left}
  → S._=₁_ f g → S._=₁_ (forth rAn f) (forth rAn g)
forth-cong {R} rAn α = PA.curry-cong (TC.mapCurry-cong (W.anima rAn)
  ((P.evaluation B ◁ W.term (SC.mapUncurry-cong α)) ▷ χ⁻¹ R))

back-cong : {R : S.CAT} (rAn : S.isAn R) {f g : S.MAP R Right}
  → S._=₁_ f g → S._=₁_ (back rAn f) (back rAn g)
back-cong {R} rAn α =
  MapCurrying.mapCurry-cong S MS rAn (PA.curry-cong
    (TC.mapUncurry-cong (P.evaluation LocalRight ◁ W.term α) ▷ χ R))

back-forth : {R : S.CAT} (rAn : S.isAn R) (h : S.MAP R Left)
  → S._=₁_ (back rAn (forth rAn h)) h
back-forth {R} rAn h = SC.mapReflect rAn _ _
  (MS.mapCurry-β rAn (P.curry (right-evaluation (forth rAn h))) thenS
    PA.reflect ((P.curry-β (right-evaluation (forth rAn h))) ⁻¹ then
      (TC.mapUncurry-cong ((P.curry-β (MT.mapCurry (W.anima rAn) (left-evaluation h))) ⁻¹) ▷ χ R) then
      (MT.mapCurry-β (W.anima rAn) (left-evaluation h) ▷ χ R) then
      T.comp-assoc (χ R) (χ⁻¹ R) (P.uncurry (MS.mapUncurry h)) then
      (P.uncurry (MS.mapUncurry h) ◁ (T.IsEquiv.sectionIso (χ-equiv R)) ⁻¹) then
      T.comp-unitʳ (P.uncurry (MS.mapUncurry h))))
  where open Calculus S using () renaming (_then_ to _thenS_)

forth-back : {R : S.CAT} (rAn : S.isAn R) (h : S.MAP R Right)
  → S._=₁_ (forth rAn (back rAn h)) h
forth-back {R} rAn h = PA.reflect
  ((P.curry-β (MT.mapCurry (W.anima rAn) (left-evaluation (back rAn h)))) ⁻¹ then
    TC.mapReflect (W.anima rAn) _ _
      (MT.mapCurry-β (W.anima rAn) (left-evaluation (back rAn h)) then
        ((P.evaluation B ◁ W.term (MS.mapCurry-β rAn (P.curry (right-evaluation h)))) ▷ χ⁻¹ R) then
        ((P.curry-β (right-evaluation h)) ⁻¹ ▷ χ⁻¹ R) then
        T.comp-assoc (χ⁻¹ R) (χ R) (MT.mapUncurry (P.uncurry h)) then
        (MT.mapUncurry (P.uncurry h) ◁ (T.IsEquiv.retractionIso (χ-equiv R)) ⁻¹) then
        T.comp-unitʳ (MT.mapUncurry (P.uncurry h))))

right-pre : {R Q : S.CAT} (h : S.MAP Q Right) (r : S.MAP R Q)
  → T._=₁_ (right-evaluation (S._∘_ h r))
    (right-evaluation h ∘ W.map (SP.productMap r (S.id X)))
right-pre {R} {Q} h r = (TC.mapUncurry-cong (PA.uncurry-pre h r) ▷ χ R) then
  (TC.mapUncurry-restrict (P.uncurry h) (W.map r) ▷ χ R) then
  T.comp-assoc (χ R) (TP.productMap (W.map r) (T.id (W.cat X))) (MT.mapUncurry (P.uncurry h)) then
  (MT.mapUncurry (P.uncurry h) ◁ (Naturality.Fixed.naturality W X r) ⁻¹) then
  (T.comp-assoc (W.map (SP.productMap r (S.id X))) (χ Q) (MT.mapUncurry (P.uncurry h))) ⁻¹

back-pre : {R Q : S.CAT} (rAn : S.isAn R) (qAn : S.isAn Q)
  (h : S.MAP Q Right) (r : S.MAP R Q)
  → S._=₁_ (back rAn (S._∘_ h r)) (S._∘_ (back qAn h) r)
back-pre rAn qAn h r = SC.mapReflect rAn _ _
  (MS.mapCurry-β rAn (P.curry (right-evaluation (S._∘_ h r))) thenS
    PA.curry-cong (right-pre h r) thenS
    PA.curry-pre (right-evaluation h) (SP.productMap r (S.id X)) thenS
    S._▷_ (S._⁻¹ (MS.mapCurry-β qAn (P.curry (right-evaluation h)))) (SP.productMap r (S.id X)) thenS
    S._⁻¹ (SC.mapUncurry-restrict (back qAn h) r))
  where open Calculus S using () renaming (_then_ to _thenS_)

module Result = Representations.Compare S Left Right (MS.map-isAn X (P.Π B))
  (P.Π-isAn (MT.map-isAn (W.cat X) B)) forth back forth-cong back-cong back-forth forth-back back-pre
  using (F; G; isEquiv; equivalence)

comparison : S.Equiv Left Right
comparison = Result.equivalence
```
