# Fibers of a pullback projection

The fiber over `y` of the second projection of a pullback of `f` and `g`
is the pullback of `f` along `g y`. Replacing that last map by a specified
isomorphic map does not change the result. This is the pullback-pasting
argument used for slice projections, before specializing to hom categories.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalNestedPullbacks as Nested

module SCT.VolumeI.Chapter02.Section01.PullbackFibers
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P

module Fiber {A B C : CAT} (f : MAP A C) (g : MAP B C)
  (y : Obj-abs B) (z : Obj-abs C) (α : (g ∘ y) =₁ z) where
  base : MAP (Pullback f g) B
  base = pullback₂
  inner : Cone f g (Pullback f g)
  inner = pullbackCone f g
  module N = Nested.Nested 𝒯 P y g f (coneSwap inner)
    (pullback-swap inner (pullbackCone-isPullback f g))
  module Change = ChangeLeft α f

  opaque
    flatten-equivalence : IsEquiv N.flatten
    flatten-equivalence = N.flatten-isEquiv
    change-equivalence : IsEquiv Change.forward
    change-equivalence = Change.forward-isEquiv
    swap-equivalence : IsEquiv (pullbackSwap z f)
    swap-equivalence = pullbackSwap-isEquiv z f

  opaque
    nested-to-target : MAP N.N (Pullback f z)
    nested-to-target = pullbackSwap z f ∘ (Change.forward ∘ N.flatten)

    nested-to-target-isEquiv : IsEquiv nested-to-target
    nested-to-target-isEquiv = equiv-compose (Change.forward ∘ N.flatten) (pullbackSwap z f)
      (equiv-compose N.flatten Change.forward flatten-equivalence change-equivalence) swap-equivalence

  opaque
    fiber-to-target : MAP (Pullback base y) (Pullback f z)
    fiber-to-target = nested-to-target ∘ pullbackSwap base y

    fiber-to-target-isEquiv : IsEquiv fiber-to-target
    fiber-to-target-isEquiv = equiv-compose (pullbackSwap base y) nested-to-target
      (pullbackSwap-isEquiv base y) nested-to-target-isEquiv

  target-to-One : MAP (Pullback f z) One
  target-to-One = pullback₁ {f = y} {base} ∘ IsEquiv.inverse nested-to-target-isEquiv

  opaque
    target-to-One-isEquiv : IsEquiv base → IsEquiv target-to-One
    target-to-One-isEquiv e = equiv-compose (IsEquiv.inverse nested-to-target-isEquiv) (pullback₁ {f = y} {base})
      (equiv-inverse nested-to-target-isEquiv) (pullback-equivalence y base e)

  opaque
    target-contractible : IsEquiv base → IsContractible (Pullback f z)
    target-contractible e = equiv-transport
      (terminal-iso target-to-One (terminate (Pullback f z))) (target-to-One-isEquiv e)
```
