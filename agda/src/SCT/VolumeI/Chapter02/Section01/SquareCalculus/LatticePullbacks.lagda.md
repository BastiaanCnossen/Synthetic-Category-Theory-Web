# The pullback diagrams defining minimum and maximum

These are the two universal endpoint cones in `cons:Lattice_Structure`.
Their apex is `[1]`, their arrow legs are `min̄` and `max̄`, and their
base leg is the identity. Universality follows by cancellation against the
equivalent slice projection.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section01.SquareCalculus.LatticePullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open Laws.PullbackStructure P

module UniversalEndpointCone {B C : CAT} (u v : MAP B C)
  (e : IsEquiv (EndpointFiber.base u v))
  (α : MorphismExpression (u ∘ id B) (v ∘ id B)) where
  module F = EndpointFiber u v
    using (base; cone; lift-base)
  cone : Cone endpoints (pair u v) B
  cone = F.cone (id B) α

  isPullback : IsPullback cone
  isPullback = equiv-cancel-left (pullbackLift cone) F.base e
    (equiv-transport ((F.lift-base (id B) α) ⁻¹) (id-isEquiv B))

module MinimumPullback = UniversalEndpointCone (const zero) (id [1]) zero-isInitial
  (retarget-expression min-expression ((const-pre zero (id [1])) ⁻¹) ((comp-unitˡ (id [1])) ⁻¹))

module MaximumPullback = UniversalEndpointCone (id [1]) (const one) one-isTerminal
  (retarget-expression max-expression ((comp-unitˡ (id [1])) ⁻¹) ((const-pre one (id [1])) ⁻¹))
```
