# The core clause of the walking-morphism axiom

The second clause of `post:Directed_Interval`, also labelled
`axiom:Groupoid_Core_Walking_Morphism`, concerns the specified endpoints:
their copairing identifies the two-point category with the core of `[1]`.
It is packaged separately from `WalkingMorphism` so that results using
only the interval and its endpoints need not assume its core clause.
Neither closure of animae under coproducts nor recognition is assumed here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.IntervalCore
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
open import SCT.VolumeI.Chapter02.Section01.CoreInclusions 𝒯 M using (core-inclusion-of-equivalent-anima)
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B
open Coproducts.CoproductStructure B
open Walking.WalkingMorphism I

intervalCore : MAP (One ⊔ One) (Core [1])
intervalCore = copair (nameMap zero) (nameMap one)

record IntervalCoreAxiom : Set m where
  field
    intervalCore-isEquiv : IsEquiv intervalCore

module Consequences (K : IntervalCoreAxiom) where
  open IntervalCoreAxiom K

  two-point-core-isEquiv : IsEquiv (coreInclusion (One ⊔ One))
  two-point-core-isEquiv = core-inclusion-of-equivalent-anima intervalCore intervalCore-isEquiv (core-isAn [1])
```

This is the consequence needed before recognition. The primitive `isAn`
witness for the two-point category is derived in Section 2.5.
