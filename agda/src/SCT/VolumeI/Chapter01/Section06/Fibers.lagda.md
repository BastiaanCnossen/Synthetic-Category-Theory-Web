# Fibers over absolute objects

The fiber in `def:Fiber_Over_Term` is the pullback of the functor along
the absolute object. The projection and its matching comparison are retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Fibers
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P

Fiber : {C D : CAT} → MAP C D → Obj-abs D → CAT
Fiber f x = Pullback f x

fiber-inclusion : {C D : CAT} (f : MAP C D) (x : Obj-abs D) → MAP (Fiber f x) C
fiber-inclusion f x = pullback₁

fiber-match : {C D : CAT} (f : MAP C D) (x : Obj-abs D)
  → (f ∘ fiber-inclusion f x) =₁ (x ∘ pullback₂)
fiber-match f x = pullbackMatch
```
