# Projecting a family to its original domain

The second projection is a functor over the base when its source has
the composite structure. Parameter substitution preserves this triangle,
with the standard comparison on the second coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section05.Currying.FamilyProjection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (parameter-base)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (parameter-over-functor)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

projection : {C B : CAT} (f : MAP C B) (X : CAT) → FunctorOver (f ∘ pr₂ {C = X}) f
projection f X = record { lift = pr₂ ; comparison = idIso (f ∘ pr₂) }

module Substitution {C B X Y : CAT} (f : MAP C B) (σ : MAP Y X) where
  Q = productMap σ (id C)
  α = parameter-base σ C
  A = comp-assoc Q pr₂ f
  source = compose-over (projection f X) (parameter-over-functor f σ)
  target = projection f Y

  abstract
    triangle-normal : FunctorLift.comparison source =₂ (f ◁ α)
    triangle-normal = cancel-right A (f ◁ α) ∙
      isoComp-cong (idIso ((f ◁ α) ∙ A))
        (isoComp-unitˡ-at (A ⁻¹) ∙
          isoComp-cong (preWhisker-idIso (f ∘ pr₂) Q) (idIso (A ⁻¹)))

    comparison : FunctorOverIso source target
    comparison = record { underlying = α
      ; compatible = triangle-normal ⁻¹ ∙ isoComp-unitˡ-at (f ◁ α) }
```
