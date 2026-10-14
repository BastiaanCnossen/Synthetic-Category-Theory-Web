# Constant cones and the mapped pullback cone

Currying a cone constant in its second parameter agrees with restricting
the mapped cone along the constant-diagram functor. This compares the
whole cones, including their matching, using the chosen curry computation.
It makes no identification with a separately chosen constant cospan map.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantConeComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (uncurryCone)
import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeCurrying as Currying
import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeReflection as Reflection
import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones as MappedCones

module At {C D B T : CAT} {f : MAP C B} {g : MAP D B}
  (A : CAT) (t : Cone f g T) where
  module Curried = Currying.CurryCone 𝒯 M ℱ (conePre (pr₁ {C = T} {D = A}) t)
    using (value; comparison)
  module Mapped = MappedCones.MappedCone 𝒯 M ℱ P A t using (value; evaluate)
  constant-cone = Curried.value
  restricted = conePre (constantDiagram A T) Mapped.value

  abstract
    evaluated-restriction : ConeIso (uncurryCone restricted) (conePre (pr₁ {C = T} {D = A}) t)
    evaluated-restriction = coneIso-compose (cone-action t (funCurry-β pr₁))
      (Mapped.evaluate (constantDiagram A T))

    comparison : ConeIso constant-cone restricted
    comparison = Reflection.ReflectCone.comparison 𝒯 M ℱ constant-cone restricted
      (coneIso-compose (coneIso-inverse evaluated-restriction) Curried.comparison)
```
