# Parameter change for paired adjunction components

The paired unit and counit commute with a change of the functor parameter.
Both endpoints use the chosen separation comparison, normalized at a
composite or at the identity as appropriate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PairedComponentParameters
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestrictionParameters as Parameters
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PairedParameterChange as Paired
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.SeparationEndpointTransport as Transport

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) where
  module A = Adjunction adj using (unit-at; counit-at)
  module Changed = Parameters.At 𝒯 M ℱ P I E S adj using (module Unit; module Counit)

  module Unit {X Y : CAT} (h : MAP X Y) where
    module Outside = Transport.Identity 𝒯 M {A = C} h using (ρ₂; module Changed; value)
    module Middle = Transport.Composite 𝒯 M h l r using (module Changed; value)
    σ : MAP (X × C) (Y × C)
    σ = productMap h (id C)
    module Component = Changed.Unit (pr₂ {Y} {C}) σ Outside.ρ₂ using (target-change; value)
    module Pair = Paired.At 𝒯 M ℱ P I E S {X = X} {Y = Y} {A = C} {B = C} h (A.unit-at (pr₂ {Y} {C})) (A.unit-at (pr₂ {X} {C}))
      Outside.ρ₂ Component.target-change Component.value using (γY; γX; value)
    abstract
      value : ExpressionIso (retarget-expression (restrict-expression Pair.γY σ)
        Outside.Changed.ν Middle.Changed.ν) (post-expression σ Pair.γX)
      value = Pair.value Outside.Changed.ν Middle.Changed.ν Outside.value Middle.value

  module Counit {X Y : CAT} (h : MAP X Y) where
    module Outside = Transport.Identity 𝒯 M {A = D} h using (ρ₂; module Changed; value)
    module Middle = Transport.Composite 𝒯 M h r l using (module Changed; value)
    σ : MAP (X × D) (Y × D)
    σ = productMap h (id D)
    module Component = Changed.Counit (pr₂ {Y} {D}) σ Outside.ρ₂ using (source-change; value)
    module Pair = Paired.At 𝒯 M ℱ P I E S {X = X} {Y = Y} {A = D} {B = D} h (A.counit-at (pr₂ {Y} {D})) (A.counit-at (pr₂ {X} {D}))
      Component.source-change Outside.ρ₂ Component.value using (γY; γX; value)
    abstract
      value : ExpressionIso (retarget-expression (restrict-expression Pair.γY σ)
        Middle.Changed.ν Outside.Changed.ν) (post-expression σ Pair.γX)
      value = Pair.value Middle.Changed.ν Outside.Changed.ν Middle.value Outside.value
```
