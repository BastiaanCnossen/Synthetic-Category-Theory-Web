# The interval under a change of context

The walking morphism has a category comparison and comparisons of its two
endpoints. Their source is the weakened terminal category, so the terminal
comparison occurs in each endpoint equation. Endpoint universal
properties, the interval core, and the Segal and Rezk witnesses require
further comparisons beyond the data recorded here.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter05.Section01.IntervalPreservation
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (IS : Walking.WalkingMorphism S) (IT : Walking.WalkingMorphism T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module IS = Walking.WalkingMorphism IS
module IT = Walking.WalkingMorphism IT

record Comparison : Set l where
  field
    category : T.Equiv (W.cat IS.[1]) IT.[1]
    zero-comparison : T._=₁_ (T._∘_ (T.Equiv.functor category) (W.map IS.zero))
      (T._∘_ IT.zero (T.Equiv.functor W.terminal))
    one-comparison : T._=₁_ (T._∘_ (T.Equiv.functor category) (W.map IS.one))
      (T._∘_ IT.one (T.Equiv.functor W.terminal))
```
