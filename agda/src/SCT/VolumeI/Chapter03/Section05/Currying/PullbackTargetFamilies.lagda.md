# Families of functors into a pullback target

Projecting from a pullback and lifting back are inverse operations on
families of triangles. The source associator is retained, so the source
structure is the one used in the relative functor category. Projection
also commutes with substitution of the parameter category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate 𝒯 M using (parameter-over)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (parameter-base)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-assoc; change-middle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BasePostcomposition 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (parameter-over-functor)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.NativePullbackTargets 𝒯 M ℱ P using (module Target; forward-composite)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module Families {A C D S : CAT} (f : MAP C S) (g : MAP D S) (r : MAP A C) where
  projection : MAP (Pullback g f) C
  projection = pullback₂
  assoc : (X : CAT) → (((f ∘ r) ∘ pr₂ {C = X}) =₁ (f ∘ (r ∘ pr₂)))
  assoc X = comp-assoc pr₂ r f

  forward : {X : CAT} → FunctorOver (r ∘ pr₂ {C = X}) projection → FunctorOver ((f ∘ r) ∘ pr₂ {C = X}) g
  forward {X} u = change-source (assoc X ⁻¹) (Target.forward f g (r ∘ pr₂) u)
  backward : {X : CAT} → FunctorOver ((f ∘ r) ∘ pr₂ {C = X}) g → FunctorOver (r ∘ pr₂ {C = X}) projection
  backward {X} v = Target.backward f g (r ∘ pr₂) (change-source (assoc X) v)

  abstract
    forward-identification : {X : CAT} {u v : FunctorOver (r ∘ pr₂ {C = X}) projection} →
      FunctorOverIso u v → FunctorOverIso (forward u) (forward v)
    forward-identification {X} Φ = change-source-iso (assoc X ⁻¹) (Target.Identification.comparison f g (r ∘ pr₂) Φ)

    backward-identification : {X : CAT} {u v : FunctorOver ((f ∘ r) ∘ pr₂ {C = X}) g} →
      FunctorOverIso u v → FunctorOverIso (backward u) (backward v)
    backward-identification {X} Φ = Target.backward-identification f g (r ∘ pr₂) (change-source-iso (assoc X) Φ)

    forward-backward : {X : CAT} (v : FunctorOver ((f ∘ r) ∘ pr₂ {C = X}) g) →
      FunctorOverIso (forward (backward v)) v
    forward-backward {X} v = compose-iso-over (source-change-inverse (assoc X) v)
      (change-source-iso (assoc X ⁻¹) (Target.forward-backward f g (r ∘ pr₂) (change-source (assoc X) v)))

    backward-forward : {X : CAT} (u : FunctorOver (r ∘ pr₂ {C = X}) projection) →
      FunctorOverIso (backward (forward u)) u
    backward-forward {X} u = compose-iso-over (Target.Recovery.comparison f g (r ∘ pr₂) u)
      (Target.backward-identification f g (r ∘ pr₂)
        (source-change-inverseʳ (assoc X) (Target.forward f g (r ∘ pr₂) u)))

    reflect : {X : CAT} (u v : FunctorOver (r ∘ pr₂ {C = X}) projection) →
      FunctorOverIso (forward u) (forward v) → FunctorOverIso u v
    reflect u v Φ = compose-iso-over (backward-forward v)
      (compose-iso-over (backward-identification Φ) (inverse-iso-over (backward-forward u)))

  module Substitution {X Y : CAT} (h : MAP Y X) where
    H : MAP (Y × A) (X × A)
    H = productMap h (id A)
    original = parameter-over-functor r h
    lifted = postbase f original
    desired = parameter-over-functor (f ∘ r) h

    abstract
      projection-comparison : ((assoc Y) ⁻¹ ∙ FunctorLift.comparison lifted) =₂
        (FunctorLift.comparison desired ∙ (assoc X ⁻¹ ▷ H))
      projection-comparison = isoComp-cong (idIso (FunctorLift.comparison desired)) ((pre-inverse (assoc X) H) ⁻¹) ∙
        move-square (assoc Y) (FunctorLift.comparison desired) (FunctorLift.comparison lifted) (assoc X ▷ H)
          (lift-assoc pr₂ pr₂ H (parameter-base h A) r f)

      comparison : (u : FunctorOver (r ∘ pr₂ {C = X}) projection) →
        FunctorOverIso (forward (compose-over u original)) (compose-over (forward u) desired)
      comparison u = compose-iso-over
        (inverse-iso-over (triangle-identification _ _ _
          (change-middle g (FunctorLift.lift (Target.forward f g (r ∘ pr₂) u)) H
            (FunctorLift.comparison (Target.forward f g (r ∘ pr₂) u))
            (FunctorLift.comparison lifted) (assoc X ⁻¹) (FunctorLift.comparison desired) (assoc Y ⁻¹)
            projection-comparison)))
        (change-source-iso (assoc Y ⁻¹) (forward-composite f g u original))
```
