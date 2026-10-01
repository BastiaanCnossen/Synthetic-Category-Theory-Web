# Lifting a triangle through an embedding

A triangle whose short edges lift through an embedding itself lifts.
Lift its specified matching, fill the resulting cocone by Segal, and
compare the two triangles using the same universal property.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.Section01.Lifting.TriangleLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (conePre; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.MapRestrictionCones 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.CoconeAssociativity 𝒯
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.RestrictionSquareEvaluation 𝒯 M ℱ P
  using (module Evaluated)
open import SCT.VolumeI.Chapter03.Section01.Lifting.CoconeLifting 𝒯 P
  using () renaming (module Lift to LiftCocone)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingSegal 𝒯 M ℱ P I E S
  using (triangleSquare; mappingTriangleCone; mappingTriangle-isPullback)
open Segal 𝒯 M ℱ P I E using ([1]; [2]; d₂; d₀)
open Segal.SegalAxiom S

module LiftTriangle {A C Γ : CAT} (Γ-an : isAn Γ)
  (f : MAP A C) (ef : IsEmbedding f) (t : MAP Γ (Map [2] C))
  (first : FunctorLift (mapPost f) (mapPre d₂ ∘ t))
  (second : FunctorLift (mapPost f) (mapPre d₀ ∘ t)) where

  private
    raw = uncurryRestriction (conePre t (mappingTriangleCone C))
    raw-lift : {h : MAP Γ (Map [1] C)} → FunctorLift (mapPost f) h →
      FunctorLift f (mapUncurry h)
    raw-lift h = record { lift = mapUncurry (FunctorLift.lift h)
      ; comparison = mapUncurryIso (FunctorLift.comparison h) ∙
          (mapPost-uncurry f (FunctorLift.lift h)) ⁻¹ }
    module L = LiftCocone f ef raw (raw-lift first) (raw-lift second)
    module Curried = CurryRestriction Γ-an L.value
    module AUniversal = UniversalCone (mappingTriangleCone A) (mappingTriangle-isPullback A)
    module CUniversal = UniversalCone (mappingTriangleCone C) (mappingTriangle-isPullback C)

  triangle : MAP Γ (Map [2] A)
  triangle = AUniversal.factor Curried.value

  raw-comparison : CoconeIso (restrictionCocone triangleSquare (mapUncurry triangle)) L.value
  raw-comparison = coconeIso-compose Curried.comparison
    (coconeIso-compose (uncurryRestrictionIso (AUniversal.factor-β Curried.value))
      (coconeIso-inverse (Evaluated.map-evaluate triangleSquare A triangle)))

  image-comparison : CoconeIso
    (uncurryRestriction (conePre (mapPost f ∘ triangle) (mappingTriangleCone C))) raw
  image-comparison = coconeIso-compose L.comparison
    (coconeIso-compose (coconeIso-post f raw-comparison)
      (coconeIso-compose (coconePost-assoc f (mapUncurry triangle) (productCocone Γ triangleSquare))
        (coconeIso-compose (restriction-action triangleSquare (mapPost-uncurry f triangle))
          (Evaluated.map-evaluate triangleSquare C (mapPost f ∘ triangle)))))

  comparison : (mapPost f ∘ triangle) =₁ t
  comparison = CUniversal.reflect _ _
    (ReflectRestriction.comparison Γ-an _ _ image-comparison)

  factorization : FunctorLift (mapPost f) t
  factorization = record { lift = triangle ; comparison = comparison }
```
