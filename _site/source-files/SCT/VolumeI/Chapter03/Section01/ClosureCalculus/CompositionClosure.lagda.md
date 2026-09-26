# Collections closed under composition

This completes `def:Collection_Of_Morphisms`. The source and target
identities must belong to the collection, and the composite of its
universal composable pair must belong to it. The latter condition is
exactly the dotted arrow in the manuscript, with its commutativity
identification retained as a `FunctorLift`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.Section01.ClosureCalculus.CompositionClosure
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPre)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I public
  using (MorphismCollection; ClosedUnderIdentities; allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingSegal 𝒯 M ℱ P I E S
  using (ComposableMorphisms; composeMorphisms; module Completion)

module ComposableIn {C : CAT} (W : MorphismCollection C) where
  open MorphismCollection W

  Composable : CAT
  Composable = Pullback (mapPre one ∘ inclusion) (mapPre zero ∘ inclusion)

  Composable-isAn : isAn Composable
  Composable-isAn = pullback-isAn _ _ collection-isAn collection-isAn (map-isAn One C)

  cone : Cone (mapPre {D = C} one) (mapPre zero) Composable
  cone = record
    { left = inclusion ∘ pullback₁
    ; right = inclusion ∘ pullback₂
    ; match = comp-assoc pullback₂ inclusion (mapPre zero) ∙
        (pullbackMatch ∙ (comp-assoc pullback₁ inclusion (mapPre one)) ⁻¹) }

  composableInclusion : MAP Composable (ComposableMorphisms C)
  composableInclusion = pullbackLift cone

  composite : MAP Composable (Map [1] C)
  composite = composeMorphisms C ∘ composableInclusion

  composite-source : (mapPre zero ∘ composite) =₁
    ((mapPre zero ∘ inclusion) ∘ pullback₁)
  composite-source = (comp-assoc pullback₁ inclusion (mapPre zero)) ⁻¹ ∙
    ((mapPre zero ◁ pullbackLift-β₁ cone) ∙
      (comp-assoc composableInclusion pullback₁ (mapPre zero) ∙
        ((Completion.compose-source C ▷ composableInclusion) ∙
          (comp-assoc composableInclusion (composeMorphisms C) (mapPre zero)) ⁻¹)))

  composite-target : (mapPre one ∘ composite) =₁
    ((mapPre one ∘ inclusion) ∘ pullback₂)
  composite-target = (comp-assoc pullback₂ inclusion (mapPre one)) ⁻¹ ∙
    ((mapPre one ◁ pullbackLift-β₂ cone) ∙
      (comp-assoc composableInclusion pullback₂ (mapPre one) ∙
        ((Completion.compose-target C ▷ composableInclusion) ∙
          (comp-assoc composableInclusion (composeMorphisms C) (mapPre one)) ⁻¹)))

record ClosedUnderComposition {C : CAT} (W : MorphismCollection C) : Set m where
  field
    identities : ClosedUnderIdentities W
    composition : FunctorLift (MorphismCollection.inclusion W) (ComposableIn.composite W)

all-morphisms-closed : (C : CAT) → ClosedUnderComposition (allMorphisms C)
all-morphisms-closed C = record
  { identities = record
      { source-identity = record { lift = _ ; comparison = comp-unitˡ _ }
      ; target-identity = record { lift = _ ; comparison = comp-unitˡ _ } }
  ; composition = record { lift = _ ; comparison = comp-unitˡ _ } }
```
