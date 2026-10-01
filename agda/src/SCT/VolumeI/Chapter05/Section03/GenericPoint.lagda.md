# Projection and generic point

Fix an anima in the ambient theory and a specified equivalence from the
sum of the local terminal category to that anima. The first projection
and the generic point are constructions from this equivalence. The
displayed square is the one used to construct the recovery map.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section03.GenericPoint
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A)) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Sums.DependentSums Q
open Action W P Q using (Σ-map; Σ-map-β; Σ-map-comp; Σ-map-cong; flatten-post)
open Calculus T using (_then_)

base : S.CAT
base = S.AN.category A

projection : (B : T.CAT) → S.MAP (Σ B) base
projection B = S._∘_ (S.Equiv.functor e) (Σ-map (T.terminate B))

generic : T.MAP T.One (W.cat base)
generic = T._∘_ (W.map (S.Equiv.functor e)) (pair T.One)

projection-β : (B : T.CAT)
  → T._=₁_ (flatten (projection B)) (T._∘_ generic (T.terminate B))
projection-β B = flatten-post (S.Equiv.functor e) (Σ-map (T.terminate B)) then
  T._◁_ (W.map (S.Equiv.functor e)) (T._⁻¹ (Σ-map-β (T.terminate B))) then
  T._⁻¹ (T.comp-assoc (T.terminate B) (pair T.One) (W.map (S.Equiv.functor e)))

projection-natural : {B C : T.CAT} (f : T.MAP B C)
  → S._=₁_ (S._∘_ (projection C) (Σ-map f)) (projection B)
projection-natural {B} {C} f = S._∙_
  (S._◁_ (S.Equiv.functor e) (Σ-map-cong (T.terminal-iso _ _)))
  (S._∙_ (S._◁_ (S.Equiv.functor e) (S._⁻¹ (Σ-map-comp f (T.terminate C))))
    (S.comp-assoc (Σ-map f) (Σ-map (T.terminate C)) (S.Equiv.functor e)))

total-functor : {B C : T.CAT} → T.MAP B C → S.FunctorLift (projection C) (projection B)
total-functor f = record { lift = Σ-map f ; comparison = projection-natural f }
```
