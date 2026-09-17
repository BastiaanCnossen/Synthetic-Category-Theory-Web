# The uniqueness clause of the pullback axiom

The sole additional field asserts the equivalence of the projection-induced
functor constructed in `PullbackComparison`. In particular, its matching
square is already fixed by joint interchange.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackData as Data
import SCT.VolumeI.Chapter01.Section05.PullbackComparison as Comparison

module SCT.VolumeI.Chapter01.Section05.PullbackLaws
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
