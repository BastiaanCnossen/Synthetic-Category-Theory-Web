# The subcategory axiom

For a collection closed under composition, `axiom:H_Subcategory_Axiom`
supplies a category with an inclusion and the displayed universal property.
We use the equivalent factorization formulation of its first clause.
`first-clause` below recovers the manuscript's projection equivalence.

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

module SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-with-section; chosen-base-change-embedding)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M
  using (mappingAction; mappingAction-natural)
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.CompositionClosure 𝒯 M ℱ P I E S
  using (MorphismCollection; ClosedUnderComposition)

presentationSquare : {A C : CAT} (W : MorphismCollection C) (i : MAP A C)
  (arrows : FunctorLift (MorphismCollection.inclusion W) (mapPost {C = [1]} i)) (D : CAT) →
  Cone (mappingAction [1] D C) (mapPost {C = Map [1] D} (MorphismCollection.inclusion W)) (Map D A)
presentationSquare {A} W i arrows D = record
  { left = mapPost i
  ; right = mapPost (FunctorLift.lift arrows) ∘ mappingAction [1] D A
  ; match = comp-assoc (mappingAction [1] D A) (mapPost (FunctorLift.lift arrows))
      (mapPost (MorphismCollection.inclusion W)) ∙
      (((mapPost-cong (FunctorLift.comparison arrows) ∙
          mapPost-comp (FunctorLift.lift arrows) (MorphismCollection.inclusion W)) ⁻¹
        ▷ mappingAction [1] D A) ∙ (mappingAction-natural [1] D i) ⁻¹) }

record SubcategoryPresentation {C : CAT} (W : MorphismCollection C) : Set (c ⊔ m) where
  field
    subcategory : CAT
    inclusion : MAP subcategory C
    arrows : FunctorLift (MorphismCollection.inclusion W) (mapPost {C = [1]} inclusion)
    universal : (D : CAT) → IsPullback (presentationSquare W inclusion arrows D)

  first-clause : IsEquiv (pullback₁ {f = mapPost {C = [1]} inclusion}
    {MorphismCollection.inclusion W})
  first-clause = embedding-with-section pullback₁
    (chosen-base-change-embedding (mapPost inclusion) (MorphismCollection.inclusion W)
      (MorphismCollection.inclusion-isEmbedding W))
    (pullbackLift sectionCone) (pullbackLift-β₁ sectionCone)
    where
    sectionCone : Cone (mapPost {C = [1]} inclusion) (MorphismCollection.inclusion W) (Map [1] subcategory)
    sectionCone = record
      { left = id (Map [1] subcategory)
      ; right = FunctorLift.lift arrows
      ; match = (FunctorLift.comparison arrows) ⁻¹ ∙ comp-unitʳ (mapPost inclusion) }

record SubcategoryAxiom : Set (c ⊔ m ⊔ a) where
  field
    generated : {C : CAT} (W : MorphismCollection C) →
      ClosedUnderComposition W → SubcategoryPresentation W
```
