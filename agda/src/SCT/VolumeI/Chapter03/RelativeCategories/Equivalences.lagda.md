# Inverting an equivalence over the base

An equivalence with a specified triangle has an inverse over the base.
Lift the identity triangle along it; reflection supplies the other
inverse comparison. Both inverse laws retain their base triangles.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Equivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.RestrictionEquivalences 𝒯 M ℱ P using (module Restriction)

module Inverse {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u : FunctorOver f g) (equivalence : IsEquiv (FunctorLift.lift u)) where
  module Chosen = Restriction.Factor g f u equivalence (identity-over f) using (value; comparison)
  inverse : FunctorOver g f
  inverse = Chosen.value

  abstract
    left-inverse : FunctorOverIso (compose-over inverse u) (identity-over f)
    left-inverse = Chosen.comparison

    right-inverse : FunctorOverIso (compose-over u inverse) (identity-over g)
    right-inverse = Restriction.Reflect.comparison g g u equivalence
      (compose-over u inverse) (identity-over g)
      (compose-iso-over (inverse-iso-over (left-unit-over u))
        (compose-iso-over (right-unit-over u)
          (compose-iso-over (postwhisker-over u left-inverse) (associator-over u inverse u))))
```
