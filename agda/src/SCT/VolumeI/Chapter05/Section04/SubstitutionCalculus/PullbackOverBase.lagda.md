# Pulling back an equivalence over the base

The induced pullback map retains the specified base triangle of its
input. Its first projection computes to the source first projection,
so it is a functor over the new base.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackFunctor as Functor
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Equivalences

module SCT.VolumeI.Chapter05.Section04.SubstitutionCalculus.PullbackOverBase
  {l : Level} (T : Theory l l l) (P : Pullbacks.PullbackStructure T) where

open View T
open Pullbacks.PullbackStructure P
open Functor T P using (CospanMap)
open Calculus T using (_then_)

module Along {A B X Y : CAT} (g : MAP B A) {p : MAP X A} {q : MAP Y A}
  (f : FunctorLift q p) where

  cospan : CospanMap g p g q
  cospan = record
    { left = id B ; right = FunctorLift.lift f ; base = id A
    ; leftSquare = comp-unitʳ g then (comp-unitˡ g) ⁻¹
    ; rightSquare = FunctorLift.comparison f then (comp-unitˡ p) ⁻¹ }

  map : MAP (Pullback g p) (Pullback g q)
  map = CospanMap.pullbackMap cospan

  over : FunctorLift (pullback₁ {f = g} {q}) (pullback₁ {f = g} {p})
  over = record { lift = map
    ; comparison = pullbackLift-β₁ (CospanMap.mapCone cospan (pullbackCone g p)) then comp-unitˡ pullback₁ }

  opaque
    map-isEquiv : IsEquiv (FunctorLift.lift f) → IsEquiv map
    map-isEquiv ef = Equivalences.CospanEquivalence.pullbackMap-isEquiv T P cospan
      (id-isEquiv B) ef (id-isEquiv A)
```
