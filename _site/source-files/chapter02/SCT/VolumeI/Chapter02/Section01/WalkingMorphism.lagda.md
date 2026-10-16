# The walking morphism

The opening walking-morphism axiom supplies the category [1] and two
absolute objects zero and one. Their copair into the existing core is
an equivalence. The arrow-family calculations use only the interval
and its endpoints. No additional anima witness is inferred from the
core clause.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.WalkingMorphism where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_)
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section04.Core using (Core)
open import SCT.VolumeI.Chapter01.Section04.Points using (name)
open import SCT.VolumeI.Chapter01.Section05.Coproducts using (_⊔_)
open import SCT.VolumeI.Chapter01.Section05.Copairing using (copair)

module _ {Γ : Context} where
  postulate
    [1] : CAT Γ
    zero one : MAP One [1]

  zero-in one-in : (P : CAT Γ) → MAP P [1]
  zero-in P = const zero
  one-in P = const one

  intervalCore : MAP (One ⊔ One) (Core [1])
  intervalCore = copair (name zero) (name one)

  postulate
    intervalCore-isEquiv : IsEquiv intervalCore
```
