# Comparing dependent constructors after a change of context

The source and target dependent constructors belong to different pairs
of theories. Their comparisons therefore use the lift of the change and
its comparison with weakening. The computation comparisons below are
separate fields: the chosen computation identifications need not agree
merely because the operations have been compared. Comparison of the
selected equivalence certificates in the universal properties is not
included in these records.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
import SCT.VolumeI.Chapter05.Section01.Routes as Routes
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums

module SCT.VolumeI.Chapter05.Section04.DependentPreservation
  {l : Level} {S T S′ T′ : Theory l l l}
  (W : Weakening S T) (W′ : Weakening S′ T′)
  (U : Weakening S S′) (H : Weakening T T′)
  (L : Routes.Comparison (compose H W) (compose W′ U))
  (P : Products.DependentProducts W) (P′ : Products.DependentProducts W′) where

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
module L = Routes.Comparison L
open T′ using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T′ using (_then_)

λ→ : (X : S.CAT) → T′.MAP (H.cat (W.cat X)) (W′.cat (U.cat X))
λ→ X = T′.Equiv.functor (L.component X)

λ← : (X : S.CAT) → T′.MAP (W′.cat (U.cat X)) (H.cat (W.cat X))
λ← X = T′.IsEquiv.inverse (T′.Equiv.isEquiv (L.component X))

local-input : {X : S.CAT} {B : T.CAT}
  → T.MAP (W.cat X) B → T′.MAP (W′.cat (U.cat X)) (H.cat B)
local-input {X} f = H.map f ∘ λ← X

record ProductComparison : Set l where
  field
    category : (B : T.CAT) → S′.Equiv (U.cat (P.Π B)) (P′.Π (H.cat B))

  arrow : (B : T.CAT) → S′.MAP (U.cat (P.Π B)) (P′.Π (H.cat B))
  arrow B = S′.Equiv.functor (category B)

  field
    evaluation : (B : T.CAT) → T′._=₁_ (H.map (P.evaluation B))
      (P′.evaluation (H.cat B) ∘ (W′.map (arrow B) ∘ λ→ (P.Π B)))
    curry : {X : S.CAT} {B : T.CAT} (f : T.MAP (W.cat X) B)
      → S′._=₁_ (S′._∘_ (arrow B) (U.map (P.curry f))) (P′.curry (local-input f))

module ProductConsequences (C : ProductComparison) where
  open ProductComparison C

  image : {X : S.CAT} {B : T.CAT} → S.MAP X (P.Π B)
    → S′.MAP (U.cat X) (P′.Π (H.cat B))
  image {B = B} h = S′._∘_ (arrow B) (U.map h)

  uncurry : {X : S.CAT} {B : T.CAT} (h : S.MAP X (P.Π B))
    → T′._=₁_ (H.map (P.uncurry h)) (P′.uncurry (image h) ∘ λ→ X)
  uncurry {X} {B} h = H.comp (W.map h) (P.evaluation B) then
    (evaluation B ▷ H.map (W.map h)) then
    T′.comp-assoc (H.map (W.map h)) (W′.map (arrow B) ∘ λ→ (P.Π B)) (P′.evaluation (H.cat B)) then
    (P′.evaluation (H.cat B) ◁
      (T′.comp-assoc (H.map (W.map h)) (λ→ (P.Π B)) (W′.map (arrow B)) then
       (W′.map (arrow B) ◁ L.naturality h) then
       (T′.comp-assoc (λ→ X) (W′.map (U.map h)) (W′.map (arrow B))) ⁻¹ then
       ((W′.comp (U.map h) (arrow B)) ⁻¹ ▷ λ→ X))) then
    (T′.comp-assoc (λ→ X) (W′.map (image h)) (P′.evaluation (H.cat B))) ⁻¹

  computation : {X : S.CAT} {B : T.CAT} (f : T.MAP (W.cat X) B)
    → T′._=₁_ (local-input f) (P′.uncurry (P′.curry (local-input f)))
  computation {X} {B} f = (H.term (P.curry-β f) ▷ λ← X) then
    (uncurry (P.curry f) ▷ λ← X) then
    T′.comp-assoc (λ← X) (λ→ X) (P′.uncurry (image (P.curry f))) then
    (P′.uncurry (image (P.curry f)) ◁
      (T′.IsEquiv.retractionIso (T′.Equiv.isEquiv (L.component X))) ⁻¹) then
    T′.comp-unitʳ (P′.uncurry (image (P.curry f))) then
    (P′.evaluation (H.cat B) ◁ W′.term (curry f))

record ProductComputations (C : ProductComparison) : Set l where
  field
    curry-β : {X : S.CAT} {B : T.CAT} (f : T.MAP (W.cat X) B)
      → T′._=₂_ (ProductConsequences.computation C f) (P′.curry-β (local-input f))

module Sum (Q : Sums.DependentSums W P) (Q′ : Sums.DependentSums W′ P′) where
  module Q = Sums.DependentSums Q
  module Q′ = Sums.DependentSums Q′

  record SumComparison : Set l where
    field
      category : (B : T.CAT) → S′.Equiv (U.cat (Q.Σ B)) (Q′.Σ (H.cat B))

    arrow : (B : T.CAT) → S′.MAP (U.cat (Q.Σ B)) (Q′.Σ (H.cat B))
    arrow B = S′.Equiv.functor (category B)

    field
      pair : (B : T.CAT) → T′._=₁_
        (W′.map (arrow B) ∘ (λ→ (Q.Σ B) ∘ H.map (Q.pair B))) (Q′.pair (H.cat B))
      extend : {B : T.CAT} {X : S.CAT} (f : T.MAP B (W.cat X))
        → S′._=₁_ (U.map (Q.extend f))
          (S′._∘_ (Q′.extend (λ→ X ∘ H.map f)) (arrow B))

  module SumConsequences (C : SumComparison) where
    open SumComparison C

    inverse : (B : T.CAT) → S′.MAP (Q′.Σ (H.cat B)) (U.cat (Q.Σ B))
    inverse B = S′.IsEquiv.inverse (S′.Equiv.isEquiv (category B))

    image : {B : T.CAT} {X : S.CAT} → S.MAP (Q.Σ B) X
      → S′.MAP (Q′.Σ (H.cat B)) (U.cat X)
    image {B} h = S′._∘_ (U.map h) (inverse B)

    image-square : {B : T.CAT} {X : S.CAT} (h : S.MAP (Q.Σ B) X)
      → S′._=₁_ (U.map h) (S′._∘_ (image h) (arrow B))
    image-square {B} h = S′._⁻¹
      (S′._∙_ (S′.comp-unitʳ (U.map h))
        (S′._∙_ (S′._◁_ (U.map h) (S′._⁻¹ (S′.IsEquiv.sectionIso (S′.Equiv.isEquiv (category B)))))
          (S′.comp-assoc (arrow B) (inverse B) (U.map h))))

    flatten : {B : T.CAT} {X : S.CAT} (h : S.MAP (Q.Σ B) X)
      → T′._=₁_ (λ→ X ∘ H.map (Q.flatten h))
        (W′.map (U.map h) ∘ (λ→ (Q.Σ B) ∘ H.map (Q.pair B)))
    flatten {B} {X} h = (λ→ X ◁ H.comp (Q.pair B) (W.map h)) then
      (T′.comp-assoc (H.map (Q.pair B)) (H.map (W.map h)) (λ→ X)) ⁻¹ then
      (L.naturality h ▷ H.map (Q.pair B)) then
      T′.comp-assoc (H.map (Q.pair B)) (λ→ (Q.Σ B)) (W′.map (U.map h))

    flatten-image : {B : T.CAT} {X : S.CAT} (h : S.MAP (Q.Σ B) X)
      → T′._=₁_ (λ→ X ∘ H.map (Q.flatten h)) (Q′.flatten (image h))
    flatten-image {B} h = flatten h then
      (W′.term (image-square h) ▷ (λ→ (Q.Σ B) ∘ H.map (Q.pair B))) then
      (W′.comp (arrow B) (image h) ▷ (λ→ (Q.Σ B) ∘ H.map (Q.pair B))) then
      T′.comp-assoc (λ→ (Q.Σ B) ∘ H.map (Q.pair B)) (W′.map (arrow B)) (W′.map (image h)) then
      (W′.map (image h) ◁ pair B)

    computation : {B : T.CAT} {X : S.CAT} (f : T.MAP B (W.cat X))
      → T′._=₁_ (λ→ X ∘ H.map f) (Q′.flatten (Q′.extend (λ→ X ∘ H.map f)))
    computation {B} {X} f = (λ→ X ◁ H.term (Q.extend-β f)) then
      flatten (Q.extend f) then
      (W′.term (extend f) ▷ (λ→ (Q.Σ B) ∘ H.map (Q.pair B))) then
      (W′.comp (arrow B) (Q′.extend (λ→ X ∘ H.map f)) ▷
        (λ→ (Q.Σ B) ∘ H.map (Q.pair B))) then
      T′.comp-assoc (λ→ (Q.Σ B) ∘ H.map (Q.pair B)) (W′.map (arrow B))
        (W′.map (Q′.extend (λ→ X ∘ H.map f))) then
      (W′.map (Q′.extend (λ→ X ∘ H.map f)) ◁ pair B)

  record SumComputations (C : SumComparison) : Set l where
    field
      extend-β : {B : T.CAT} {X : S.CAT} (f : T.MAP B (W.cat X))
        → T′._=₂_ (SumConsequences.computation C f) (Q′.extend-β (λ→ X ∘ H.map f))
```
