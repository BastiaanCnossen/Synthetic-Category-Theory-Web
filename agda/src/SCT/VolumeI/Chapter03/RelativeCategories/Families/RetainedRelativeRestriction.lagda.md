# Changing the parameter of a retained relative family

Retaining a parameter commutes with changing that parameter. We choose
the comparison by its product projections and recover its native base
triangle from the comparison after forgetting the parameter. This also
compares composition of the restricted families with restriction of
their composite.

These are comparisons of the stated endpoints. Coherence between
successive substitutions is a separate claim.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (parameter-base)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies 𝒯 M ℱ P
  using (module Retained; module ProjectionReflection)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
  using (parameter-over-functor)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right)

module ParameterProjection {X Y B S : CAT} (g : MAP B S) (σ : MAP Y X) where
  param = parameter-over-functor g σ
  projectionX : FunctorOver (g ∘ pr₂ {C = X}) g
  projectionX = record { lift = pr₂ ; comparison = idIso (g ∘ pr₂) }
  projectionY : FunctorOver (g ∘ pr₂ {C = Y}) g
  projectionY = record { lift = pr₂ ; comparison = idIso (g ∘ pr₂) }
  β = parameter-base σ B
  associator = comp-assoc (FunctorLift.lift param) pr₂ g
  module Reflect = ProjectionReflection pr₂ g param param
  opaque
    triangle : FunctorLift.comparison (compose-over projectionX param) =₂ (g ◁ β)
    triangle = cancel-right associator (g ◁ β) ∙ Reflect.Triangle.normalize param

    comparison : FunctorOverIso (compose-over projectionX param) projectionY
    comparison = record { underlying = β ; compatible = triangle ⁻¹ ∙ isoComp-unitˡ-at (g ◁ β) }

-- The comparison keeps the base triangle and has specified product images.
-- No coherence between successive substitutions is claimed here.
module Restriction {X Y A B S : CAT} (f : MAP A S) (g : MAP B S)
  (σ : MAP Y X) (v : FunctorOver (f ∘ pr₂ {C = X}) g) where
  paramA = parameter-over-functor f σ
  paramB = parameter-over-functor g σ
  module V = Retained f g v
  restricted = compose-over v paramA
  module W = Retained f g restricted
  module Projection = ParameterProjection g σ
  source = compose-over paramB W.over
  target = compose-over V.over paramA
  module Reflect = ProjectionReflection pr₂ g source target

  opaque
    source-to-common : FunctorOverIso (compose-over Reflect.projection source) restricted
    source-to-common = compose-iso-over W.forget-retained
      (compose-iso-over (prewhisker-over W.over Projection.comparison)
        (inverse-iso-over (associator-over W.over paramB Reflect.projection)))

    target-to-common : FunctorOverIso (compose-over Reflect.projection target) restricted
    target-to-common = compose-iso-over (prewhisker-over paramA V.forget-retained)
      (inverse-iso-over (associator-over paramA V.over Reflect.projection))

    projected : FunctorOverIso (compose-over Reflect.projection source) (compose-over Reflect.projection target)
    projected = compose-iso-over (inverse-iso-over target-to-common) source-to-common

  first-source = (σ ◁ pair-β₁ pr₁ W.value) ∙
    (comp-assoc W.lift pr₁ σ ∙
      ((pair-β₁ (σ ∘ pr₁) (id B ∘ pr₂) ▷ W.lift) ∙
        (comp-assoc W.lift (FunctorLift.lift paramB) pr₁) ⁻¹))
  first-target = pair-β₁ (σ ∘ pr₁) (id A ∘ pr₂) ∙
    ((pair-β₁ pr₁ V.value ▷ FunctorLift.lift paramA) ∙
      (comp-assoc (FunctorLift.lift paramA) V.lift pr₁) ⁻¹)
  first = first-target ⁻¹ ∙ first-source
  second = FunctorOverIso.underlying projected
  underlying = pair-iso first second

  comparison : FunctorOverIso source target
  comparison = Reflect.FromImage.comparison projected underlying (pair-iso-β₂ first second)

module CompositeFamilyRestriction {X Y A B C S : CAT}
  (f : MAP A S) (g : MAP B S) (h : MAP C S) (σ : MAP Y X)
  (u : FunctorOver (f ∘ pr₂ {C = X}) g)
  (v : FunctorOver (g ∘ pr₂ {C = X}) h) where
  paramA = parameter-over-functor f σ
  paramB = parameter-over-functor g σ
  module U = Retained f g u
  restricted-u = compose-over u paramA
  restricted-v = compose-over v paramB
  module RestrictedU = Retained f g restricted-u
  module R = Restriction f g σ u

  source : FunctorOver (f ∘ pr₂ {C = Y}) h
  source = compose-over restricted-v RestrictedU.over

  target : FunctorOver (f ∘ pr₂ {C = Y}) h
  target = compose-over (compose-over v U.over) paramA

  opaque
    comparison : FunctorOverIso source target
    comparison = compose-iso-over (inverse-iso-over (associator-over paramA U.over v))
      (compose-iso-over (postwhisker-over v R.comparison)
        (associator-over RestrictedU.over paramB v))
```
