# Projecting a change of argument

Adjoining a parameter to a native functor commutes with forgetting that
parameter. The second product projection gives the comparison; cancelling
the source associator proves its compatibility with the base triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section05.Currying.ArgumentFamilyProjection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)
open import SCT.VolumeI.Chapter03.Section05.Currying.FamilyProjection 𝒯 M ℱ P using (projection)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.RetainedRelativeFamilies 𝒯 M ℱ P using (module ProjectionReflection)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

module Project {A B S : CAT} {f : MAP A S} {g : MAP B S}
  (u : FunctorOver f g) (X : CAT) where
  e = FunctorLift.lift u
  θ = FunctorLift.comparison u
  argument = Argument.family u X
  Q = FunctorLift.lift argument
  β = pair-β₂ (id X ∘ pr₁) (e ∘ pr₂)
  d = θ ▷ pr₂ {C = X}
  A₀ = comp-assoc (pr₂ {C = X}) e g
  b = g ◁ β
  A₁ = comp-assoc Q pr₂ g
  middle = d ∙ A₀ ⁻¹
  normal = middle ∙ b
  source = compose-over (projection g X) argument
  target = compose-over u (projection f X)
  module Reflect = ProjectionReflection pr₂ g argument argument using (module Triangle)

  opaque
    source-normal : FunctorLift.comparison source =₂ normal
    source-normal = cancel-right A₁ normal ∙
      (isoComp-cong
        ((isoComp-assoc-at middle b A₁) ⁻¹ ∙
          (isoComp-assoc-at d (A₀ ⁻¹) (b ∙ A₁)) ⁻¹)
        (idIso (A₁ ⁻¹)) ∙ Reflect.Triangle.normalize argument)

    target-normal : FunctorLift.comparison target =₂ middle
    target-normal = isoComp-unitˡ-at middle

    comparison : FunctorOverIso source target
    comparison = record { underlying = β
      ; compatible = source-normal ⁻¹ ∙ isoComp-cong target-normal (idIso b) }
```
