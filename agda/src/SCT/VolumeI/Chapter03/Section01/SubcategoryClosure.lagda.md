# The morphisms of a subcategory are closed under composition

For `ex:Morphisms_In_Subcategory`, lift the two short edges of the ambient
composite triangle. The subcategory inclusion is an embedding, so the
specified middle matching lifts too. The lifted triangle supplies the
required composite. Identities follow from functoriality.

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

module SCT.VolumeI.Chapter03.Section01.SubcategoryClosure
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open Segal 𝒯 M ℱ P I E using ([2]; d₀; d₁; d₂)
open import SCT.VolumeI.Chapter03.Section01.Subcategories 𝒯 M P I
  using (IsSubcategory; subcategory-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.CompositionClosure 𝒯 M ℱ P I E S
  using (ClosedUnderComposition; module ComposableIn)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingSegal 𝒯 M ℱ P I E S
  using (composeMorphisms; module Completion)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.Lifting.TriangleLifting 𝒯 M ℱ P I E S
  using (module LiftTriangle)

module Closure {A C : CAT} (f : MAP A C) (sub : IsSubcategory f) where
  W = subcategoryMorphisms f sub
  module Pair = ComposableIn W
  triangle = Completion.j C ∘ Pair.composableInclusion

  first : FunctorLift (mapPost f) (mapPre d₂ ∘ triangle)
  first = record { lift = pullback₁
    ; comparison = ((pullbackLift-β₁ Pair.cone) ∙
        ((Completion.first-edge C ▷ Pair.composableInclusion) ∙
          (comp-assoc Pair.composableInclusion (Completion.j C) (mapPre d₂)) ⁻¹)) ⁻¹ }
  second : FunctorLift (mapPost f) (mapPre d₀ ∘ triangle)
  second = record { lift = pullback₂
    ; comparison = ((pullbackLift-β₂ Pair.cone) ∙
        ((Completion.second-edge C ▷ Pair.composableInclusion) ∙
          (comp-assoc Pair.composableInclusion (Completion.j C) (mapPre d₀)) ⁻¹)) ⁻¹ }

  module Lift = LiftTriangle Pair.Composable-isAn f (subcategory-isEmbedding f sub)
    triangle first second

  composite-lift : FunctorLift (mapPost f) Pair.composite
  composite-lift = record { lift = mapPre d₁ ∘ Lift.triangle
    ; comparison = (comp-assoc Pair.composableInclusion (Completion.j C) (mapPre d₁)) ⁻¹ ∙
        ((mapPre d₁ ◁ Lift.comparison) ∙
          (comp-assoc Lift.triangle (mapPost f) (mapPre d₁) ∙
            (((mapPre-mapPost d₁ f) ⁻¹ ▷ Lift.triangle) ∙
              (comp-assoc Lift.triangle (mapPre d₁) (mapPost f)) ⁻¹))) }

  closed : ClosedUnderComposition W
  closed = record
    { identities = record
        { source-identity = record { lift = mapPre (const zero)
            ; comparison = (mapPre-mapPost (const zero) f) ⁻¹ }
        ; target-identity = record { lift = mapPre (const one)
            ; comparison = (mapPre-mapPost (const one) f) ⁻¹ } }
    ; composition = composite-lift }

subcategory-morphisms-closed : {A C : CAT} (f : MAP A C) (sub : IsSubcategory f) →
  ClosedUnderComposition (subcategoryMorphisms f sub)
subcategory-morphisms-closed = Closure.closed
```
