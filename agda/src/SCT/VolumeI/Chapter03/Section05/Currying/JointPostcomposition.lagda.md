# Postcomposition and joint relative composition

Postcomposing a composite relative family agrees with first
postcomposing its outer family. Evaluate both constructions on the
common parameter and apply the native associator. Coherent lifting
then gives a single comparison of the two functors, with its full
evaluated computation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.Families.CoherentRelativeFamilyLifting as CoherentLifting

module SCT.VolumeI.Chapter03.Section05.Currying.JointPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family; curried-beta; postcompose-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.JointComposition 𝒯 M ℱ P using (module Joint)

module Postcomposition {A B C D S : CAT} (f : MAP A S) (g : MAP B S)
  {h : MAP C S} {k : MAP D S} (w : FunctorOver h k) where
  parameter = FunOver g h × FunOver f g
  module Old = Joint f g h using (functor; inner; outer; composite; module Inner)
  module New = Joint f g k using (functor; module At)
  module InnerPost = Postcompose g w using (functor)
  module WholePost = Postcompose f w using (functor)
  outer-name : MAP parameter (FunOver g k)
  outer-name = InnerPost.functor ∘ pr₁
  module NewAt = New.At pr₂ outer-name using (evaluation)
  source : MAP parameter (FunOver f k)
  source = WholePost.functor ∘ Old.functor
  parameter-map : MAP parameter (FunOver g k × FunOver f g)
  parameter-map = pair outer-name pr₂
  target : MAP parameter (FunOver f k)
  target = New.functor ∘ parameter-map
  common = compose-over w Old.composite

  opaque
    source-evaluation : FunctorOverIso (family f k source) common
    source-evaluation = compose-iso-over (postwhisker-over w (curried-beta f h Old.composite))
      (postcompose-family f w Old.functor)

    target-evaluation : FunctorOverIso (family f k target) common
    target-evaluation = compose-iso-over (associator-over Old.Inner.over Old.outer w)
      (compose-iso-over (prewhisker-over Old.Inner.over (postcompose-family g w pr₁))
        NewAt.evaluation)

    family-comparison : FunctorOverIso (family f k source) (family f k target)
    family-comparison = compose-iso-over (inverse-iso-over target-evaluation) source-evaluation

  module Lifted = CoherentLifting.Families 𝒯 M ℱ P f k source target
    using (action; lift; computation)

  opaque
    comparison : source =₁ target
    comparison = Lifted.lift family-comparison

    computation : FunctorOverIso₂ (Lifted.action comparison) family-comparison
    computation = Lifted.computation family-comparison
```
