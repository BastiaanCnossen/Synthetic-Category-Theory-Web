# Preservation of the dependent-product equivalence witness

The identification comparison in the dependent-product axiom has a
chosen inverse and two chosen inverse identifications. We compare that
entire certificate after changing context. The source and target of its
comparison functor are constructed from the comparisons already given;
no new category equivalences are assumed here.

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
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section04.DependentPreservation as Preservation

module SCT.VolumeI.Chapter05.Section04.ProductUniversalPreservation
  {l : Level} {S T S′ T′ : Theory l l l}
  (W : Weakening S T) (W′ : Weakening S′ T′)
  (U : Weakening S S′) (H : Weakening T T′)
  (UP : PreservesProducts U) (HP : PreservesProducts H)
  (L : Routes.Comparison (compose H W) (compose W′ U))
  (P : Products.DependentProducts W) (P′ : Products.DependentProducts W′)
  (C : Preservation.ProductComparison W W′ U H L P P′) where

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
module C = Preservation.ProductComparison C
module Consequences = Preservation.ProductConsequences W W′ U H L P P′ C
module Outer = Objects U UP
module Inner = Objects H HP
module E = Equivalences W′ P′ using (Π-equiv)

absolute-input : (X : S.CAT) → Outer.Object
absolute-input X = record { source = X ; target = U.cat X
  ; comparison = record { functor = S′.id (U.cat X) ; isEquiv = S′.id-isEquiv (U.cat X) } }

product-output : (B : T.CAT) → Outer.Object
product-output B = record { source = P.Π B ; target = P′.Π (H.cat B) ; comparison = C.category B }

absolute-arrow : {X : S.CAT} {B : T.CAT} (h : S.MAP X (P.Π B))
  → Outer.Arrow (absolute-input X) (product-output B)
absolute-arrow h = record { source = h ; target = Consequences.image h
  ; square = S′._⁻¹ (S′.comp-unitʳ (Consequences.image h)) }

local-input : (X : S.CAT) → Inner.Object
local-input X = record { source = W.cat X ; target = W′.cat (U.cat X)
  ; comparison = Routes.Comparison.component L X }

local-output : (B : T.CAT) → Inner.Object
local-output B = record { source = B ; target = H.cat B
  ; comparison = record { functor = T′.id (H.cat B) ; isEquiv = T′.id-isEquiv (H.cat B) } }

local-arrow : {X : S.CAT} {B : T.CAT} (h : S.MAP X (P.Π B))
  → Inner.Arrow (local-input X) (local-output B)
local-arrow h = record { source = P.uncurry h ; target = P′.uncurry (Consequences.image h)
  ; square = T′._∙_ (Consequences.uncurry h) (T′.comp-unitˡ (H.map (P.uncurry h))) }

domain : {X : S.CAT} {B : T.CAT} (h k : S.MAP X (P.Π B)) → Outer.Object
domain h k = Outer.identifications (absolute-arrow h) (absolute-arrow k)

codomain : {X : S.CAT} {B : T.CAT} (h k : S.MAP X (P.Π B)) → Outer.Object
codomain h k = record
  { source = P.Π (T._＝_ (P.uncurry h) (P.uncurry k))
  ; target = P′.Π (T′._＝_ (P′.uncurry (Consequences.image h)) (P′.uncurry (Consequences.image k)))
  ; comparison = Rebased.join S′
      (C.category (T._＝_ (P.uncurry h) (P.uncurry k)))
      (E.Π-equiv (Inner.Object.comparison (Inner.identifications (local-arrow h) (local-arrow k)))) }

record Comparison : Set l where
  field
    square : {X : S.CAT} {B : T.CAT} (h k : S.MAP X (P.Π B))
      → S′._=₁_ (S′._∘_ (Outer.Object.arrow (codomain h k)) (U.map (P.comparison h k)))
        (S′._∘_ (P′.comparison (Consequences.image h) (Consequences.image k))
          (Outer.Object.arrow (domain h k)))

  arrow : {X : S.CAT} {B : T.CAT} (h k : S.MAP X (P.Π B))
    → Outer.Arrow (domain h k) (codomain h k)
  arrow h k = record { source = P.comparison h k
    ; target = P′.comparison (Consequences.image h) (Consequences.image k) ; square = square h k }

  field
    certificate : {X : S.CAT} {B : T.CAT} (h k : S.MAP X (P.Π B))
      → Witnesses.EquivalenceComparison U UP (arrow h k)
        (P.comparison-isEquiv h k) (P′.comparison-isEquiv (Consequences.image h) (Consequences.image k))
```
