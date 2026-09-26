# Every functor preserves isomorphisms

This is `prop:Every_Functor_Preserves_Isomorphisms`. Rezk identifies
isomorphisms with constant arrows. Restriction of the mapping action
then shows, for the entire anima of functors at once, that the action
on isomorphisms lands in isomorphisms. This supplies a section of the
defining embedding, hence an equivalence.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.PreservingIsomorphismMaps
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-with-section)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingRestriction 𝒯 M using (mappingAction-restrict)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
open WithRezk R
open Rezk 𝒯 M ℱ P I E using (Iso)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategoryCharacterization 𝒯 M ℱ P I E S
  using (full-subcategory-on-equivalent-objects)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)

module Preservation (C D : CAT) where
  qC = identityComparison C
  qD = identityComparison D
  πC = isomorphismInclusion C
  πD = isomorphismInclusion D
  action = Inverting.restriction (isomorphisms C) D
  on-objects = mappingAction One C D
  candidate = mapPost qD ∘ on-objects
  chosen = equiv-lift (mapPre-isEquiv {E = Core (Iso D)} qC
    (identityComparison-isEquiv C)) candidate

  family : MAP (Map C D) (Map (Core (Iso C)) (Core (Iso D)))
  family = FunctorLift.lift chosen

  restricted-action : (mapPre qC ∘ action) =₁ (mapPost (constantMap D) ∘ on-objects)
  restricted-action = (mappingAction-restrict (terminate [1]) C D) ⁻¹ ∙
    ((mapPre-cong (identityComparison-over-morphisms C) ▷ mappingAction [1] C D) ∙
      ((mapPre-comp qC πC ▷ mappingAction [1] C D) ∙
        (comp-assoc (mappingAction [1] C D) (mapPre πC) (mapPre qC)) ⁻¹))

  restricted-family : (mapPre qC ∘ (mapPost πD ∘ family)) =₁ (mapPost (constantMap D) ∘ on-objects)
  restricted-family = (mapPost-cong (identityComparison-over-morphisms D) ▷ on-objects) ∙
    ((mapPost-comp qD πD ▷ on-objects) ∙
      ((comp-assoc on-objects (mapPost qD) (mapPost πD)) ⁻¹ ∙
        ((mapPost πD ◁ FunctorLift.comparison chosen) ∙
          (comp-assoc family (mapPre qC) (mapPost πD) ∙
            ((mapPre-mapPost qC πD ▷ family) ∙
              (comp-assoc family (mapPost πD) (mapPre qC)) ⁻¹)))))

  comparison : (mapPost πD ∘ family) =₁ action
  comparison = equiv-reflect (mapPre-isEquiv qC (identityComparison-isEquiv C)) _ _
    (restricted-action ⁻¹ ∙ restricted-family)

  cone : Cone action (mapPost πD) (Map C D)
  cone = record { left = id (Map C D) ; right = family
    ; match = comparison ⁻¹ ∙ comp-unitʳ action }

  abstract
    maps-isEquiv : IsEquiv (Inverting.inclusion (isomorphisms C) D)
    maps-isEquiv = embedding-with-section _ (Inverting.inclusion-isEmbedding (isomorphisms C) D)
      (pullbackLift cone) (pullbackLift-β₁ cone)
```
