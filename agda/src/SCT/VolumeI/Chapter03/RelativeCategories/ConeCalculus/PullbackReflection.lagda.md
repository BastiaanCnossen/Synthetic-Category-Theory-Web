# Reflecting a comparison of relative pullback cones

Lift the whole underlying cone comparison, retaining both projected
images. Compatibility with the first projection's base triangle then
recovers an identification over the base. The second image remains the
specified right-leg comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (module Lift)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionReflection 𝒯 M ℱ P using (module Recover)

module Reflect {X C D E S : CAT} {t : MAP X S} {f : MAP C S} {g : MAP D S} {h : MAP E S}
  (u : FunctorOver f h) (v : FunctorOver g h) where
  module PB = RelativePullback u v
  module Between (x y : FunctorOver t PB.projection)
    (first : FunctorOverIso (compose-over PB.first x) (compose-over PB.first y))
    (cones : ConeIso (conePre (FunctorLift.lift x) (pullbackCone PB.left-map PB.right-map))
      (conePre (FunctorLift.lift y) (pullbackCone PB.left-map PB.right-map)))
    (first-image : ConeIso.leftIso cones =₂ FunctorOverIso.underlying first) where
    module Lifted = Lift (FunctorLift.lift x) (FunctorLift.lift y) cones
    abstract
      comparison : FunctorOverIso x y
      comparison = Recover.comparison PB.first first Lifted.lift (first-image ∙ Lifted.left-image)

      right-image : (PB.second-map ◁ FunctorOverIso.underlying comparison) =₂ ConeIso.rightIso cones
      right-image = Lifted.right-image ∙ (postWhisker PB.second-map ◁
        Recover.underlying-image PB.first first Lifted.lift (first-image ∙ Lifted.left-image))
```
