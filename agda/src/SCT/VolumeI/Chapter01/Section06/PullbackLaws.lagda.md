# The uniqueness clause of the pullback axiom

The sole additional field, `pullback-isoMap-isEquiv`, asserts the equivalence
of the projection-induced functor constructed in `PullbackComparison`.
Its matching square has already been constructed using fixed-outer
interchange with the chosen cone's matching isomorphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackData as Data
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparison

module SCT.VolumeI.Chapter01.Section06.PullbackLaws
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯

record PullbackLaws (P : Data.PullbackData 𝒯) : Set (c ⊔ m) where
  open Data.PullbackData P
  field
    pullback-isoMap-isEquiv : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
      (h k : MAP T (Pullback f g)) → IsEquiv (Comparison.IsoComparison.forward 𝒯 P h k)

record PullbackStructure : Set (c ⊔ m ⊔ a) where
  field
    dataPullback : Data.PullbackData 𝒯
    lawsPullback : PullbackLaws dataPullback
  open Data.PullbackData dataPullback public
  open PullbackLaws lawsPullback public
```
