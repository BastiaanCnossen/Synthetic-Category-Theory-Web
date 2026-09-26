# Functors from a groupoid invert all morphisms

Every morphism of the source is represented by its isomorphism collection.
Extend the factorization supplied by preservation of isomorphisms across
that equivalence. This gives a section of the inverting mapping anima.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.InvertingFromGroupoids
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
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-with-section)
open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R using (IsGroupoid)
open Rezk 𝒯 M ℱ P I E using (Iso)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M using (mappingAction)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q using (isomorphismInclusion)
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingGroupoids 𝒯 M ℱ P I E S Q R using (isomorphisms-of-groupoid)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.PreservingIsomorphisms 𝒯 M ℱ P I E S Q R using (module Preservation)

module FromGroupoid (C : CAT) (groupoid : IsGroupoid C) (D : CAT) where
  module Preserve = Preservation C D using (family; comparison)
  module All = Inverting (allMorphisms C) D using (restriction; inclusion; inclusion-isEmbedding)
  πC = isomorphismInclusion C
  πD = isomorphismInclusion D
  restriction-equivalence = mapPre-isEquiv {E = Core (Iso D)} πC (isomorphisms-of-groupoid C groupoid)
  chosen = equiv-lift restriction-equivalence Preserve.family

  family : MAP (Map C D) (Map (Map [1] C) (Core (Iso D)))
  family = FunctorLift.lift chosen

  restriction-identity : All.restriction =₁ mappingAction [1] C D
  restriction-identity = comp-unitˡ (mappingAction [1] C D) ∙
    (mapPre-id (Map [1] C) (Map [1] D) ▷ mappingAction [1] C D)

  comparison : (mapPost πD ∘ family) =₁ All.restriction
  comparison = equiv-reflect (mapPre-isEquiv πC (isomorphisms-of-groupoid C groupoid)) _ _
    (((mapPre πC ◁ restriction-identity) ⁻¹) ∙
      (Preserve.comparison ∙
        ((mapPost πD ◁ FunctorLift.comparison chosen) ∙
          (comp-assoc family (mapPre πC) (mapPost πD) ∙
            ((mapPre-mapPost πC πD ▷ family) ∙
              (comp-assoc family (mapPost πD) (mapPre πC)) ⁻¹)))))

  cone : Cone All.restriction (mapPost πD) (Map C D)
  cone = record { left = id (Map C D) ; right = family
    ; match = comparison ⁻¹ ∙ comp-unitʳ All.restriction }

  abstract
    inclusion-isEquiv : IsEquiv All.inclusion
    inclusion-isEquiv = embedding-with-section All.inclusion All.inclusion-isEmbedding
      (pullbackLift cone) (pullbackLift-β₁ cone)
```
