# Preservation of the dependent-sum equivalence witness

The dependent-sum constructor comparison changes the domain of an
absolute functor. We use its inverse to express the transported functor
with the target sum as domain. The induced identification-anima
comparisons then type the comparison of the whole selected equivalence
certificate in the sum axiom.

The square for the compound comparison functor is still supplied as
data. Identifying it with the recursively generated expression comparison
is a remaining obligation. The selected certificate is compared relative
to that square.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
import SCT.VolumeI.Chapter05.Section01.Routes as Routes
import SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonObjects as Objects
import SCT.VolumeI.Chapter05.Section01.Expressions.RebasedPaths as Rebased
import SCT.VolumeI.Chapter05.Section01.ComparisonWitnesses as Witnesses
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section04.DependentPreservation as Preservation

module SCT.VolumeI.Chapter05.Section04.SumUniversalPreservation
  {l : Level} {S T S′ T′ : Theory l l l}
  (W : Weakening S T) (W′ : Weakening S′ T′)
  (U : Weakening S S′) (H : Weakening T T′)
  (UP : PreservesProducts U) (HP : PreservesProducts H)
  (L : Routes.Comparison (compose H W) (compose W′ U))
  (P : Products.DependentProducts W) (P′ : Products.DependentProducts W′)
  (Q : Sums.DependentSums W P) (Q′ : Sums.DependentSums W′ P′)
  (PC : Preservation.ProductComparison W W′ U H L P P′)
  (C : Preservation.Sum.SumComparison W W′ U H L P P′ Q Q′) where

private
  module S = View S
  module T = View T
  module S′ = View S′
  module T′ = View T′
module W = Weakening W
module W′ = Weakening W′
module U = Weakening U
module H = Weakening H
module P = Products.DependentProducts P
module P′ = Products.DependentProducts P′
module Q = Sums.DependentSums Q
module Q′ = Sums.DependentSums Q′
module PC = Preservation.ProductComparison PC
module C = Preservation.Sum.SumComparison C
module Consequences = Preservation.Sum.SumConsequences W W′ U H L P P′ Q Q′ C
module Outer = Objects U UP
module Inner = Objects H HP
module E = Equivalences W′ P′ using (Π-equiv)

sum-input : (B : T.CAT) → Outer.Object
sum-input B = record { source = Q.Σ B ; target = Q′.Σ (H.cat B) ; comparison = C.category B }

absolute-output : (X : S.CAT) → Outer.Object
absolute-output X = record { source = X ; target = U.cat X
  ; comparison = record { functor = S′.id (U.cat X) ; isEquiv = S′.id-isEquiv (U.cat X) } }

absolute-arrow : {B : T.CAT} {X : S.CAT} (h : S.MAP (Q.Σ B) X)
  → Outer.Arrow (sum-input B) (absolute-output X)
absolute-arrow h = record { source = h ; target = Consequences.image h
  ; square = S′._∙_ (Consequences.image-square h) (S′.comp-unitˡ (U.map h)) }

local-input : (B : T.CAT) → Inner.Object
local-input B = record { source = B ; target = H.cat B
  ; comparison = record { functor = T′.id (H.cat B) ; isEquiv = T′.id-isEquiv (H.cat B) } }

local-output : (X : S.CAT) → Inner.Object
local-output X = record { source = W.cat X ; target = W′.cat (U.cat X)
  ; comparison = Routes.Comparison.component L X }

local-arrow : {B : T.CAT} {X : S.CAT} (h : S.MAP (Q.Σ B) X)
  → Inner.Arrow (local-input B) (local-output X)
local-arrow h = record { source = Q.flatten h ; target = Q′.flatten (Consequences.image h)
  ; square = T′._∙_ (T′._⁻¹ (T′.comp-unitʳ (Q′.flatten (Consequences.image h))))
      (Consequences.flatten-image h) }

domain : {B : T.CAT} {X : S.CAT} (h k : S.MAP (Q.Σ B) X) → Outer.Object
domain h k = Outer.identifications (absolute-arrow h) (absolute-arrow k)

codomain : {B : T.CAT} {X : S.CAT} (h k : S.MAP (Q.Σ B) X) → Outer.Object
codomain h k = record
  { source = P.Π (T._＝_ (Q.flatten h) (Q.flatten k))
  ; target = P′.Π (T′._＝_ (Q′.flatten (Consequences.image h)) (Q′.flatten (Consequences.image k)))
  ; comparison = Rebased.join S′
      (PC.category (T._＝_ (Q.flatten h) (Q.flatten k)))
      (E.Π-equiv (Inner.Object.comparison (Inner.identifications (local-arrow h) (local-arrow k)))) }

record Comparison : Set l where
  field
    square : {B : T.CAT} {X : S.CAT} (h k : S.MAP (Q.Σ B) X)
      → S′._=₁_ (S′._∘_ (Outer.Object.arrow (codomain h k)) (U.map (Q.comparison h k)))
        (S′._∘_ (Q′.comparison (Consequences.image h) (Consequences.image k))
          (Outer.Object.arrow (domain h k)))

  arrow : {B : T.CAT} {X : S.CAT} (h k : S.MAP (Q.Σ B) X)
    → Outer.Arrow (domain h k) (codomain h k)
  arrow h k = record { source = Q.comparison h k
    ; target = Q′.comparison (Consequences.image h) (Consequences.image k) ; square = square h k }

  field
    certificate : {B : T.CAT} {X : S.CAT} (h k : S.MAP (Q.Σ B) X)
      → Witnesses.EquivalenceComparison U UP (arrow h k)
        (Q.comparison-isEquiv h k) (Q′.comparison-isEquiv (Consequences.image h) (Consequences.image k))
```
