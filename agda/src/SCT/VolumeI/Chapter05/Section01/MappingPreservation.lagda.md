# Preservation of mapping animae

The comparison for a mapping anima includes evaluation and the chosen
currying operation. The comparison for its computation identification
and for its identification-anima universal property are separate data.
In particular, preservation of the selected inverse certificate is not
deduced from preservation of the underlying equivalence.

The universal-property square is currently supplied separately. Its
identification with the recursive comparison for the defined uncurrying
functor remains to be established.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
import SCT.VolumeI.Chapter05.Section01.Products as Products
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ProductNaturality as ProductNaturality
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonObjects as Objects
import SCT.VolumeI.Chapter05.Section01.Expressions.RebasedPaths as Rebased
import SCT.VolumeI.Chapter05.Section01.ComparisonWitnesses as Witnesses
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup

module SCT.VolumeI.Chapter05.Section01.MappingPreservation
  {l : Level} {S T : Theory l l l} (W : Weakening S T) (WP : PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module SM = Setup S MS
  using (Map; mapCurry; mapCurry-β; mapEval; mapUncurry; mapUncurry-isoMap; mapUncurry-isoMap-isEquiv;
    productMap)
module TM = Setup T MT
  using (Map; mapCurry; mapCurry-β; mapPost; mapPost-isEquiv; mapPre; mapPre-isEquiv; mapUncurry;
    mapUncurry-cong; mapUncurry-isoMap; mapUncurry-isoMap-isEquiv; mapUncurry-restrict; productMap)
module O = Objects W WP
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

product-comparison = Products.Comparison.comparison W
product-isEquiv = PreservesProducts.comparison-isEquiv WP
product-inverse : (X C : S.CAT) → T.MAP (T._×_ (W.cat X) (W.cat C)) (W.cat (S._×_ X C))
product-inverse X C = T.IsEquiv.inverse (product-isEquiv X C)

record MappingComparison : Set l where
  field
    category : (C D : S.CAT) → T.Equiv (W.cat (SM.Map C D)) (TM.Map (W.cat C) (W.cat D))
  arrow : (C D : S.CAT) → T.MAP (W.cat (SM.Map C D)) (TM.Map (W.cat C) (W.cat D))
  arrow C D = T.Equiv.functor (category C D)
  field
    evaluation : (C D : S.CAT) → T._=₁_ (W.map (SM.mapEval {C} {D}))
      (TM.mapUncurry (arrow C D) ∘ product-comparison (SM.Map C D) C)
    curry : {X C D : S.CAT} (xAn : S.isAn X) (f : S.MAP (S._×_ X C) D)
      → T._=₁_ (arrow C D ∘ W.map (SM.mapCurry xAn f))
        (TM.mapCurry (W.anima xAn) (W.map f ∘ product-inverse X C))

module Comparisons (K : MappingComparison) where
  open MappingComparison K

  fixed : S.CAT → O.Object
  fixed C = record { source = C ; target = W.cat C
    ; comparison = record { functor = T.id (W.cat C) ; isEquiv = T.id-isEquiv (W.cat C) } }

  mapping : O.Object → O.Object → O.Object
  mapping C D = record
    { source = SM.Map (O.Object.source C) (O.Object.source D)
    ; target = TM.Map (O.Object.target C) (O.Object.target D)
    ; comparison = Rebased.join T (category (O.Object.source C) (O.Object.source D))
        (record
          { functor = TM.mapPost (O.Object.arrow D) ∘ TM.mapPre (T.IsEquiv.inverse (T.Equiv.isEquiv (O.Object.comparison C)))
          ; isEquiv = T.equiv-compose _ _
              (TM.mapPre-isEquiv _ (T.equiv-inverse (T.Equiv.isEquiv (O.Object.comparison C))))
              (TM.mapPost-isEquiv _ (T.Equiv.isEquiv (O.Object.comparison D))) }) }

  direct-mapping : (C D : S.CAT) → O.Object
  direct-mapping C D = record { source = SM.Map C D ; target = TM.Map (W.cat C) (W.cat D) ; comparison = category C D }

  product : (X C : S.CAT) → O.Object
  product X C = record { source = S._×_ X C ; target = T._×_ (W.cat X) (W.cat C)
    ; comparison = record { functor = product-comparison X C ; isEquiv = product-isEquiv X C } }

  image : {X C D : S.CAT} → S.MAP X (SM.Map C D) → T.MAP (W.cat X) (TM.Map (W.cat C) (W.cat D))
  image {C = C} {D} h = arrow C D ∘ W.map h

  input : {X C D : S.CAT} (h : S.MAP X (SM.Map C D)) → O.Arrow (fixed X) (direct-mapping C D)
  input h = record { source = h ; target = image h ; square = (T.comp-unitʳ (image h)) ⁻¹ }

  uncurry : {X C D : S.CAT} (h : S.MAP X (SM.Map C D))
    → T._=₁_ (W.map (SM.mapUncurry h)) (TM.mapUncurry (image h) ∘ product-comparison X C)
  uncurry {X} {C} {D} h = W.comp (SM.productMap h (S.id C)) SM.mapEval then
    (evaluation C D ▷ W.map (SM.productMap h (S.id C))) then
    T.comp-assoc (W.map (SM.productMap h (S.id C))) (product-comparison (SM.Map C D) C) (TM.mapUncurry (arrow C D)) then
    (TM.mapUncurry (arrow C D) ◁ ProductNaturality.Fixed.naturality W C h) then
    (T.comp-assoc (product-comparison X C) (TM.productMap (W.map h) (T.id (W.cat C))) (TM.mapUncurry (arrow C D))) ⁻¹ then
    ((TM.mapUncurry-restrict (arrow C D) (W.map h)) ⁻¹ ▷ product-comparison X C)

  uncurried : {X C D : S.CAT} (h : S.MAP X (SM.Map C D)) → O.Arrow (product X C) (fixed D)
  uncurried h = record { source = SM.mapUncurry h ; target = TM.mapUncurry (image h)
    ; square = T.comp-unitˡ _ then uncurry h }

  weakened-family : {X C D : S.CAT} (f : S.MAP (S._×_ X C) D) → O.Arrow (product X C) (fixed D)
  weakened-family {X} {C} f = record { source = f ; target = W.map f ∘ product-inverse X C
    ; square = T.comp-unitˡ _ then (T.comp-unitʳ (W.map f)) ⁻¹ then
        (W.map f ◁ T.IsEquiv.sectionIso (product-isEquiv X C)) then
        (T.comp-assoc (product-comparison X C) (product-inverse X C) (W.map f)) ⁻¹ }

  curried-family : {X C D : S.CAT} (xAn : S.isAn X) (f : S.MAP (S._×_ X C) D)
    → O.Arrow (product X C) (fixed D)
  curried-family {X} {C} xAn f = record
    { source = SM.mapUncurry (SM.mapCurry xAn f)
    ; target = TM.mapUncurry (TM.mapCurry (W.anima xAn) (W.map f ∘ product-inverse X C))
    ; square = T.comp-unitˡ _ then uncurry (SM.mapCurry xAn f) then
        (TM.mapUncurry-cong (curry xAn f) ▷ product-comparison X C) }

  record Computation : Set l where
    field
      beta : {X C D : S.CAT} (xAn : S.isAn X) (f : S.MAP (S._×_ X C) D)
        → Witnesses.CellComparison W WP (curried-family xAn f) (weakened-family f)
          (SM.mapCurry-β xAn f) (TM.mapCurry-β (W.anima xAn) (W.map f ∘ product-inverse X C))

  record Universal : Set l where
    field
      square : {X C D : S.CAT} (h k : S.MAP X (SM.Map C D))
        → T._=₁_ (O.Object.arrow (O.identifications (uncurried h) (uncurried k)) ∘ W.map (SM.mapUncurry-isoMap h k))
            (TM.mapUncurry-isoMap (image h) (image k) ∘ O.Object.arrow (O.identifications (input h) (input k)))
    comparison : {X C D : S.CAT} (h k : S.MAP X (SM.Map C D))
      → O.Arrow (O.identifications (input h) (input k)) (O.identifications (uncurried h) (uncurried k))
    comparison h k = record { source = SM.mapUncurry-isoMap h k ; target = TM.mapUncurry-isoMap (image h) (image k) ; square = square h k }
    field
      certificate : {X C D : S.CAT} (xAn : S.isAn X) (h k : S.MAP X (SM.Map C D))
        → Witnesses.EquivalenceComparison W WP (comparison h k)
          (SM.mapUncurry-isoMap-isEquiv xAn h k) (TM.mapUncurry-isoMap-isEquiv (W.anima xAn) (image h) (image k))
```
