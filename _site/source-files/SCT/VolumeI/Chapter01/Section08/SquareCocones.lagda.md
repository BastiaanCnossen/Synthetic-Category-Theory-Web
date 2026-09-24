# The cocone of a square

The right and bottom arrows, together with the specified commutativity
isomorphism, form the ordinary cocone underlying a square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section08.SquareCocones
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯

squareCocone : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  Square u l r v → Cocone u l D
squareCocone {r = r} {v} s = record
  { left = r ; right = v ; match = Square.commute s }
```
