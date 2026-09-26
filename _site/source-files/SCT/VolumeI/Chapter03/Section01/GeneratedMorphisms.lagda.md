# The morphisms of the generated subcategory

For `cor:Morphisms_In_Subcategory_Constructor`, apply the universal
property with `D = [1]`. Its action on arrows is determined by the three
endomorphisms of `[1]`: the source identity, the arrow itself, and the
target identity. Closure under identities therefore lifts that whole
action through the collection. The resulting factorization supplies a
section of the comparison on morphisms. Since both inclusions are
embeddings, the comparison is an embedding and hence an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section01.IntervalCore as Interval
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.Section01.GeneratedMorphisms
  {c ℓm a : Level} (𝒯 : Theory c ℓm a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (K : Interval.IntervalCoreAxiom 𝒯 M B I) (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (nameMap)
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPost; mapPre; mapPre-id)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-cong; embedding-reflect; embedding-with-section; module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P
  using (map-preserves-embedding)
open import SCT.VolumeI.Chapter02.Section01.TriangleCore 𝒯 M ℱ P B U I E Q K
  using (intervalEndomorphisms-isEquiv)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
  using (MorphismCollection; ClosedUnderIdentities)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M
  using (mappingAction; mappingAction-restrict-point)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.FiniteMappingLifts 𝒯 M B
  using (retarget-lift; lift-core-family; module ThreePoints)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryPresentation; presentationSquare)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S
  using (module Presented)

module Morphisms {C : CAT} (W : MorphismCollection C) (closed : ClosedUnderIdentities W)
  (A : SubcategoryPresentation W) where
  open MorphismCollection W renaming (collection to X; inclusion to m; inclusion-isEmbedding to m-embedding)
  open SubcategoryPresentation A renaming (subcategory to G; inclusion to i)
  j = FunctorLift.lift arrows
  action = mappingAction [1] [1] C ∘ m
  module Finite = ThreePoints (nameMap (const zero)) (nameMap (id [1])) (nameMap (const one))
    intervalEndomorphisms-isEquiv using (lift-three)

  at-point : (f : MAP [1] [1]) → FunctorLift m (mapPre f ∘ m) →
    FunctorLift (mapPost m) (mapPre (nameMap f) ∘ action)
  at-point f l = lift-core-family collection-isAn (map-isAn [1] C) m _
    (retarget-lift ((mappingAction-restrict-point f m collection-isAn) ⁻¹) l)

  at-identity : FunctorLift m (mapPre (id [1]) ∘ m)
  at-identity = record { lift = id X
    ; comparison = (comp-unitˡ m ∙ (mapPre-id [1] C ▷ m)) ⁻¹ ∙ comp-unitʳ m }

  action-lift : FunctorLift (mapPost m) action
  action-lift = Finite.lift-three m action
    (at-point (const zero) (ClosedUnderIdentities.source-identity closed))
    (at-point (id [1]) at-identity)
    (at-point (const one) (ClosedUnderIdentities.target-identity closed))

  cone : Cone (mappingAction [1] [1] C) (mapPost m) X
  cone = record { left = m ; right = FunctorLift.lift action-lift
    ; match = (FunctorLift.comparison action-lift) ⁻¹ }

  module Universal = UniversalCone (presentationSquare W i arrows [1]) (universal [1])
  section : MAP X (Map [1] G)
  section = Universal.factor cone

  section-over-C : (mapPost i ∘ section) =₁ m
  section-over-C = ConeIso.leftIso (Universal.factor-β cone)

  section-comparison : (j ∘ section) =₁ id X
  section-comparison = embedding-reflect m m-embedding _ _
    ((comp-unitʳ m) ⁻¹ ∙
      (section-over-C ∙ ((FunctorLift.comparison arrows ▷ section) ∙
        (comp-assoc section j m) ⁻¹)))

  comparison-isEmbedding : IsEmbedding j
  comparison-isEmbedding = LeftCancellation.cancel j m m-embedding
    (embedding-cong ((FunctorLift.comparison arrows) ⁻¹)
      (map-preserves-embedding [1] i (Presented.inclusion-isEmbedding W A)))

  comparison-isEquiv : IsEquiv j
  comparison-isEquiv = embedding-with-section j comparison-isEmbedding section section-comparison

generated-morphisms-isEquiv : {C : CAT} (W : MorphismCollection C)
  (closed : ClosedUnderIdentities W) (A : SubcategoryPresentation W) →
  IsEquiv (FunctorLift.lift (SubcategoryPresentation.arrows A))
generated-morphisms-isEquiv = Morphisms.comparison-isEquiv
```
