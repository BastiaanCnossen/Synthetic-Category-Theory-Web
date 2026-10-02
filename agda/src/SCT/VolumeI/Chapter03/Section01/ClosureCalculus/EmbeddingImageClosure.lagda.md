# Closure of the morphism image of an embedding

A collection presenting the arrows of an embedded category is closed
under composition. Transport its two arrows into that category, lift the
ambient triangle with its specified matching, and transport its long
edge back to the collection. This also applies to the embedded core, and,
with identity transports, to the morphisms of a subcategory. The
transports are compositions of factorizations; the long edge and the
identities are carried along the commutation of restriction and
postcomposition.

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

module SCT.VolumeI.Chapter03.Section01.ClosureCalculus.EmbeddingImageClosure
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open Segal 𝒯 M ℱ P I E using ([2]; d₀; d₁; d₂)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section03.FactorizationCalculus
  vocabulary terminal products productLaws composition
  using (lift-retarget; lift-restrict; lift-compose; lift-along-square)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.CompositionClosure 𝒯 M ℱ P I E S
  using (ClosedUnderComposition; module ComposableIn)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingSegal 𝒯 M ℱ P I E S using (module Completion)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.Lifting.TriangleLifting 𝒯 M ℱ P I E S using (module LiftTriangle)

module Closure {A C : CAT} (f : MAP A C) (ef : IsEmbedding f) (W : MorphismCollection C)
  (toImage : FunctorLift (mapPost {C = [1]} f) (MorphismCollection.inclusion W))
  (fromImage : FunctorLift (MorphismCollection.inclusion W) (mapPost {C = [1]} f)) where
  inclusion = MorphismCollection.inclusion W
  to = FunctorLift.lift toImage
  from = FunctorLift.lift fromImage
  module Pair = ComposableIn W
  triangle = Completion.j C ∘ Pair.composableInclusion

  short-lift : (p : MAP Pair.Composable (MorphismCollection.collection W))
    (edge : MAP (Map [2] C) (Map [1] C)) →
    (edge ∘ triangle) =₁ (inclusion ∘ p) → FunctorLift (mapPost f) (edge ∘ triangle)
  short-lift p edge β = lift-retarget (β ⁻¹) (lift-restrict toImage p)
  first = short-lift pullback₁ (mapPre d₂)
    (pullbackLift-β₁ Pair.cone ∙
      ((Completion.first-edge C ▷ Pair.composableInclusion) ∙
        (comp-assoc Pair.composableInclusion (Completion.j C) (mapPre d₂)) ⁻¹))
  second = short-lift pullback₂ (mapPre d₀)
    (pullbackLift-β₂ Pair.cone ∙
      ((Completion.second-edge C ▷ Pair.composableInclusion) ∙
        (comp-assoc Pair.composableInclusion (Completion.j C) (mapPre d₀)) ⁻¹))
  module Lift = LiftTriangle Pair.Composable-isAn f ef triangle first second

  composite-image : FunctorLift (mapPost f) Pair.composite
  composite-image = lift-retarget
    ((comp-assoc Pair.composableInclusion (Completion.j C) (mapPre d₁)) ⁻¹)
    (lift-along-square (mapPre-mapPost d₁ f) Lift.factorization)

  composite-lift : FunctorLift inclusion Pair.composite
  composite-lift = lift-compose fromImage composite-image

  identity-lift : (x : Obj-abs [1]) → FunctorLift inclusion (mapPre (const x) ∘ inclusion)
  identity-lift x = lift-compose fromImage
    (lift-along-square (mapPre-mapPost (const x) f) toImage)

  closed : ClosedUnderComposition W
  closed = record { identities = record
      { source-identity = identity-lift zero ; target-identity = identity-lift one }
    ; composition = composite-lift }
```
