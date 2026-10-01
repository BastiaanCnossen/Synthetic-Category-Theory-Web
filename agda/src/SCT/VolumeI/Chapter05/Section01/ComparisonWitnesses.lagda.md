# Comparison witnesses with changing category expressions

An identification is a functor from the terminal category to an
identification anima. Its comparison is therefore another comparison of
functors, after comparing those two category expressions. The operation
`cell` exposes this step so that it can be repeated at the next level.

The same pattern records preservation of a selected equivalence witness:
its inverse functor, section identification, and retraction identification
each receive a comparison. These are data, not consequences of the
underlying functor being an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
import SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonObjects as Objects

module SCT.VolumeI.Chapter05.Section01.ComparisonWitnesses
  {l : Level} {S T : Theory l l l} (W : Weakening S T) (P : PreservesProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Objects W P using (Object; Arrow; one; identity; compose; identifications)

CellComparison : {C D : Object} (f g : Arrow C D)
  → S._=₁_ (Arrow.source f) (Arrow.source g)
  → T._=₁_ (Arrow.target f) (Arrow.target g) → Set l
CellComparison f g α β = T._=₁_
  (T._∘_ (Object.arrow (identifications f g)) (W.map α))
  (T._∘_ β (Object.arrow one))

cell : {C D : Object} (f g : Arrow C D)
  (α : S._=₁_ (Arrow.source f) (Arrow.source g))
  (β : T._=₁_ (Arrow.target f) (Arrow.target g))
  → CellComparison f g α β → Arrow one (identifications f g)
cell f g α β w = record { source = α ; target = β ; square = w }

record EquivalenceComparison {C D : Object} (f : Arrow C D)
  (source : S.IsEquiv (Arrow.source f)) (target : T.IsEquiv (Arrow.target f)) : Set l where
  field
    inverse : T._=₁_
      (T._∘_ (Object.arrow C) (W.map (S.IsEquiv.inverse source)))
      (T._∘_ (T.IsEquiv.inverse target) (Object.arrow D))

  inverse-arrow : Arrow D C
  inverse-arrow = record
    { source = S.IsEquiv.inverse source ; target = T.IsEquiv.inverse target ; square = inverse }

  field
    section : CellComparison (identity C) (compose inverse-arrow f)
      (S.IsEquiv.sectionIso source) (T.IsEquiv.sectionIso target)
    retraction : CellComparison (identity D) (compose f inverse-arrow)
      (S.IsEquiv.retractionIso source) (T.IsEquiv.retractionIso target)
```
