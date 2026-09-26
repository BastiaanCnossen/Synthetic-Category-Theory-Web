# Changing the structure of a native triangle

Postcompose the specified triangle with an identification of the source
structure functor. This operation changes the structure, retaining the
underlying functor, and carries identifications over the base along it.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P

open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (parameter-over-functor)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate 𝒯 M using (parameter-over)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (parameter-base)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (change-middle; lift-base-outer)

open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

change-source : {C D S : CAT} {f f′ : MAP C S} {g : MAP D S} →
  f =₁ f′ → FunctorOver f g → FunctorOver f′ g
change-source α u = record { lift = FunctorLift.lift u ; comparison = α ∙ FunctorLift.comparison u }

change-source-iso : {C D S : CAT} {f f′ : MAP C S} {g : MAP D S}
  (α : f =₁ f′) {u v : FunctorOver f g} → FunctorOverIso u v →
  FunctorOverIso (change-source α u) (change-source α v)
change-source-iso {g = g} α {u} {v} Φ = record { underlying = FunctorOverIso.underlying Φ
  ; compatible = isoComp-cong (idIso α) (FunctorOverIso.compatible Φ) ∙
      isoComp-assoc-at α (FunctorLift.comparison v) (g ◁ FunctorOverIso.underlying Φ) }

triangle-identification : {C D S : CAT} {f : MAP C S} {g : MAP D S} (h : MAP C D)
  (θ ψ : (g ∘ h) =₁ f) → θ =₂ ψ →
  FunctorOverIso (record { lift = h ; comparison = θ }) (record { lift = h ; comparison = ψ })
triangle-identification {g = g} h θ ψ χ = record { underlying = idIso h
  ; compatible = χ ⁻¹ ∙ (isoComp-unitʳ-at ψ ∙ isoComp-cong (idIso ψ) (postWhisker-idIso g h)) }

abstract
  parameter-change : {X Y C D S : CAT} {f f′ : MAP C S} {g : MAP D S}
    (α : f =₁ f′) (r : MAP Y X) (u : FunctorOver (f ∘ pr₂ {C = X}) g) →
    FunctorOverIso
      (compose-over (change-source (α ▷ pr₂) u) (parameter-over-functor f′ r))
      (change-source (α ▷ pr₂) (compose-over u (parameter-over-functor f r)))
  parameter-change {C = C} {f = f} {f′} {g} α r u = triangle-identification _ _ _
    (change-middle g (FunctorLift.lift u) (productMap r (id C))
      (FunctorLift.comparison u) (parameter-over r f) (α ▷ pr₂)
      (parameter-over r f′) (α ▷ pr₂)
      ((lift-base-outer pr₂ pr₂ (productMap r (id C)) (parameter-base r C) α) ⁻¹))

abstract
  source-change-inverse : {C D S : CAT} {f f′ : MAP C S} {g : MAP D S}
    (α : f =₁ f′) (u : FunctorOver f g) → FunctorOverIso (change-source (α ⁻¹) (change-source α u)) u
  source-change-inverse α u = triangle-identification _ _ _ (cancel-left α (FunctorLift.comparison u))

  source-change-inverseʳ : {C D S : CAT} {f f′ : MAP C S} {g : MAP D S}
    (α : f =₁ f′) (u : FunctorOver f′ g) → FunctorOverIso (change-source α (change-source (α ⁻¹) u)) u
  source-change-inverseʳ α u = triangle-identification _ _ _ (cancel-inverse α (FunctorLift.comparison u))
```
