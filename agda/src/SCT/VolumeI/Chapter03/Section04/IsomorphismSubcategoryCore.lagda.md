# Objects of the subcategory of isomorphisms

This is the diagram argument in `(5) ⇒ (6)` of
`prop:Equivalent_Conditions_Geometric_Realization`. The inclusion of
the core sends every arrow into the isomorphism collection, so factors
through its spanned subcategory. Taking cores gives a section of the
map on cores, which is an embedding and hence an equivalence.

The same diagram compares the constant-arrow functor of the subcategory
with the Rezk equivalence. Its arrow comparison is an embedding and its
composite with constant arrows is an equivalence. It follows that both
are equivalences. Thus this special case does not need a separate
enumeration of the interval's three endomorphisms.

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
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

module SCT.VolumeI.Chapter03.Section04.IsomorphismSubcategoryCore
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-cong; embedding-reflect; embedding-with-section; module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P using (map-preserves-embedding)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S using (module Presented)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
  using (isomorphisms; isomorphismInclusion; isomorphismInclusion-isEmbedding; constantMap; module WithRezk)
open WithRezk R
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.IsomorphismClosure 𝒯 M ℱ P I E S Q R N using (module At)
open import SCT.VolumeI.Chapter03.Section02.SpannedCore 𝒯 M ℱ P I E S using (core-reflect)

module CoreComparison (C : CAT) (A : SubcategoryPresentation (isomorphisms C)) where
  G = SubcategoryPresentation.subcategory A
  i = SubcategoryPresentation.inclusion A
  j = FunctorLift.lift (SubcategoryPresentation.arrows A)
  j-over = FunctorLift.comparison (SubcategoryPresentation.arrows A)
  w = isomorphismInclusion C
  w-embedding = isomorphismInclusion-isEmbedding C
  i-embedding = Presented.inclusion-isEmbedding (isomorphisms C) A
  module Lift = Presented.Factor (isomorphisms C) A (coreInclusion C) (At.from-core-arrows C)
    using (factor; comparison)

  from-core : MAP (Core C) G
  from-core = Lift.factor

  from-core-over-C : (i ∘ from-core) =₁ coreInclusion C
  from-core-over-C = Lift.comparison

  module CoreFactor = CoreLift (core-isAn C) from-core using (lift; comparison)
  core-map = mapPost {C = One} i

  core-section : (core-map ∘ CoreFactor.lift) =₁ id (Core C)
  core-section = core-reflect (core-isAn C) _ _
    ((comp-unitʳ (coreInclusion C)) ⁻¹ ∙
      (from-core-over-C ∙
        ((i ◁ CoreFactor.comparison) ∙
          (comp-assoc CoreFactor.lift (coreInclusion G) i ∙
            ((coreInclusion-natural i ▷ CoreFactor.lift) ∙
              (comp-assoc CoreFactor.lift core-map (coreInclusion C)) ⁻¹)))))

  abstract
    core-map-isEquiv : IsEquiv core-map
    core-map-isEquiv = embedding-with-section core-map
      (map-preserves-embedding One i i-embedding) CoreFactor.lift core-section

  triangle : (j ∘ constantMap G) =₁ (identityComparison C ∘ core-map)
  triangle = embedding-reflect w w-embedding _ _
    (comp-assoc core-map (identityComparison C) w ∙
      ((identityComparison-over-morphisms C ⁻¹ ▷ core-map) ∙
        ((mapPre-mapPost (terminate [1]) i) ⁻¹ ∙
          ((j-over ▷ constantMap G) ∙ (comp-assoc (constantMap G) j w) ⁻¹))))

  composite-isEquiv : IsEquiv (j ∘ constantMap G)
  composite-isEquiv = equiv-transport (triangle ⁻¹)
    (equiv-compose core-map (identityComparison C) core-map-isEquiv (identityComparison-isEquiv C))

  arrow-embedding : IsEmbedding j
  arrow-embedding = LeftCancellation.cancel j w w-embedding
    (embedding-cong (j-over ⁻¹) (map-preserves-embedding [1] i i-embedding))
  chosen = equiv-lift composite-isEquiv (id _)

  abstract
    arrows-isEquiv : IsEquiv j
    arrows-isEquiv = embedding-with-section j arrow-embedding
      (constantMap G ∘ FunctorLift.lift chosen)
      (FunctorLift.comparison chosen ∙ (comp-assoc (FunctorLift.lift chosen) (constantMap G) j) ⁻¹)

    constantMap-isEquiv : IsEquiv (constantMap G)
    constantMap-isEquiv = equiv-cancel-left (constantMap G) j arrows-isEquiv composite-isEquiv

  module IfGroupoid (gAn : isAn G) where
    abstract
      from-core-isEquiv : IsEquiv from-core
      from-core-isEquiv = equiv-transport CoreFactor.comparison
        (equiv-compose CoreFactor.lift (coreInclusion G)
          (equiv-cancel-left CoreFactor.lift core-map core-map-isEquiv
            (equiv-transport (core-section ⁻¹) (id-isEquiv (Core C))))
          (core-of-anima G gAn))
```
