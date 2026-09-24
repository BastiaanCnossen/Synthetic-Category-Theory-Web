# The walking morphism

`post:Directed_Interval` supplies a category and its two absolute objects.
Their constant terms are available in any common categorical context.
Initiality of zero and terminality of one are stated separately, after
slice categories have been defined.
The remaining clause of the same opening axiom, specifying the interval's
core by its two endpoints, is recorded in `IntervalCore`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter02.Section01.WalkingMorphism
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯

record WalkingMorphism : Set (c ⊔ m) where
  field
    [1] : CAT
    zero one : Obj-abs [1]

  zero-in : (Γ : CAT) → MAP Γ [1]
  zero-in Γ = const zero

  one-in : (Γ : CAT) → MAP Γ [1]
  one-in Γ = const one
```
