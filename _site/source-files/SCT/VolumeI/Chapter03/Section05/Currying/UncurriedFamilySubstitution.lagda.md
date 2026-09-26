# Uncurrying whole families commutes with parameter change

First uncurry the composite source triangle, then reassociate its
parameter product. The retained comparison of the two product routes
makes this a comparison over the base. It applies to the entire family,
not only to its absolute instances.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.UncurriedFamilySubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (parameter-over-functor)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Triangle; module Family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingComposition 𝒯 M ℱ P using (module Composite)
open import SCT.VolumeI.Chapter03.Section05.Currying.UncurriedParameterComparison 𝒯 M ℱ P using (module Parameter)

module Substitution {K S C B X Y : CAT} (r : MAP C B) (f : MAP K (Fun S B))
  (σ : MAP Y X) (v : FunctorOver (f ∘ pr₂ {C = X}) (funPost r)) where
  original = parameter-over-functor f σ
  uncurried = Uncurry.value S B original
  changed = parameter-over-functor (funUncurry f) σ
  evaluated = Triangle.value r (f ∘ pr₂ {C = X}) v
  module FX = Family r f X using (insertion; value)
  module FY = Family r f Y using (insertion; value)

  abstract
    comparison : FunctorOverIso (FY.value (compose-over v original)) (compose-over (FX.value v) changed)
    comparison = compose-iso-over (inverse-iso-over (associator-over changed FX.insertion evaluated))
      (compose-iso-over (postwhisker-over evaluated (Parameter.comparison r f σ))
        (compose-iso-over (associator-over FY.insertion uncurried evaluated)
          (prewhisker-over FY.insertion (Composite.comparison r original v))))
```
