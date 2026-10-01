# Generic fibers of functors over the base

A functor over the base carries its specified triangle. This triangle
supplies the right square of a map of cospans; taking the induced map on
pullbacks constructs the generic-fiber functor. An underlying
equivalence induces an equivalence on generic fibers.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Core as Core
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.GenericFiber as Fiber
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackFunctor as Functor
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Equivalences

module SCT.VolumeI.Chapter05.Section03.GenericFiberFunctor
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PB : Pullbacks.PullbackStructure T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module G = Point W P Q A e using (base; generic)
module F = Fiber W P Q A e (Pullbacks.PullbackStructure.dataPullback PB) using (Fiber; fiber-inclusion)
open Pullbacks.PullbackStructure PB
open Functor T PB using (CospanMap)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

module Over {X Y : S.CAT} {p : S.MAP X G.base} {q : S.MAP Y G.base}
  (f : S.FunctorLift q p) where
  module f = S.FunctorLift f

  cospan : CospanMap G.generic (W.map p) G.generic (W.map q)
  cospan = record
    { left = T.id T.One ; right = W.map f.lift ; base = T.id (W.cat G.base)
    ; leftSquare = T.comp-unitʳ G.generic then (T.comp-unitˡ G.generic) ⁻¹
    ; rightSquare = (W.comp f.lift q) ⁻¹ then W.term f.comparison then
        (T.comp-unitˡ (W.map p)) ⁻¹ }

  map : T.MAP (F.Fiber p) (F.Fiber q)
  map = CospanMap.pullbackMap cospan

  inclusion : T._=₁_ (F.fiber-inclusion q ∘ map) (W.map f.lift ∘ F.fiber-inclusion p)
  inclusion = pullbackLift-β₂ (CospanMap.mapCone cospan (pullbackCone G.generic (W.map p)))

  map-isEquiv : S.IsEquiv f.lift → T.IsEquiv map
  map-isEquiv ef = Equivalences.CospanEquivalence.pullbackMap-isEquiv T PB cospan
    (T.id-isEquiv T.One) (Core.Results.preservesEquiv W ef) (T.id-isEquiv (W.cat G.base))
```
