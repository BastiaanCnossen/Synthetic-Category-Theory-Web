# Inverting the walking morphism

The inverting mapping anima for all arrows of `[1]` is its subanima of
constant arrows. For one inclusion, a constant functor factors through
the groupoid `One`, so inverts every arrow. For the other inclusion,
evaluate the family of inverted arrows at the identity functor of `[1]`.
Rezk identifies the resulting isomorphism with a constant arrow.

This proves the mapping-anima calculation used in
`axiom:N_Fundamental_Groupoid_Axiom`. It avoids enumerating the three
arrows of `[1]`: evaluation at its identity functor gives the necessary
condition directly, and preservation of isomorphisms gives sufficiency.

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

module SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.InvertingInterval
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Composition 𝒯 M using (applyTerm; applyTerm-cong)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (embedding-reflect; embedding-cong; module LeftCancellation; equivalence-isEmbedding)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure 𝒯 M ℱ P I E R using (terminal-isGroupoid)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M
  using (mappingAction; mappingAction-at; apply-mapPost; compose-named-right)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
  using (allMorphisms; PreservesMorphisms)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
  using (constantMap; isomorphismInclusion; isomorphismInclusion-isEmbedding; module WithRezk)
open WithRezk R
open import SCT.VolumeI.Chapter03.Section03.InvertingFunctors 𝒯 M ℱ P I E S Q using (module Inverting)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingRestriction 𝒯 M ℱ P I E S Q using (module Restrict)
open import SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.InvertingFromGroupoids 𝒯 M ℱ P I E S Q R using (module FromGroupoid)

module Into (D : CAT) where
  module All = Inverting (allMorphisms [1]) D
  module Point = Inverting (allMorphisms One) D
  π = isomorphismInclusion D

  terminal-preserves : PreservesMorphisms (terminate [1]) (allMorphisms [1]) (allMorphisms One)
  terminal-preserves = record { lift = mapPost (terminate [1])
    ; comparison = (comp-unitʳ (mapPost (terminate [1]))) ⁻¹ ∙ comp-unitˡ (mapPost (terminate [1])) }
  module Restriction = Restrict (allMorphisms [1]) (allMorphisms One)
    (terminate [1]) terminal-preserves D using (maps; maps-comparison)
  point-equivalence = FromGroupoid.inclusion-isEquiv One terminal-isGroupoid D
  point-lift = equiv-lift point-equivalence (id (Core D))

  abstract
    constants : MAP (Core D) All.maps
    constants = Restriction.maps ∘ FunctorLift.lift point-lift
  
    constants-comparison : (All.inclusion ∘ constants) =₁ constantMap D
    constants-comparison = comp-unitʳ (constantMap D) ∙
      ((constantMap D ◁ FunctorLift.comparison point-lift) ∙
        (comp-assoc (FunctorLift.lift point-lift) Point.inclusion (constantMap D) ∙
          ((Restriction.maps-comparison ▷ FunctorLift.lift point-lift) ∙
            (comp-assoc (FunctorLift.lift point-lift) Restriction.maps All.inclusion) ⁻¹)))

  restriction-identity : All.restriction =₁ mappingAction [1] [1] D
  restriction-identity = comp-unitˡ (mappingAction [1] [1] D) ∙
    (mapPre-id (Map [1] [1]) (Map [1] D) ▷ mappingAction [1] [1] D)

  inverted-identity = applyTerm (pullback₂ {f = All.restriction} {mapPost π})
    (const (nameMap (id [1])))

  inverted-identity-comparison : (π ∘ inverted-identity) =₁ All.inclusion
  inverted-identity-comparison = comp-unitˡ All.inclusion ∙
    ((mapPre-id [1] D ▷ All.inclusion) ∙
      (compose-named-right (id [1]) All.inclusion All.maps-isAn ∙
        (mappingAction-at All.inclusion (const (nameMap (id [1]))) ∙
          (applyTerm-cong (restriction-identity ▷ All.inclusion) (idIso _) ∙
            (applyTerm-cong (pullbackMatch ⁻¹) (idIso _) ∙
              (apply-mapPost π pullback₂ (const (nameMap (id [1])))) ⁻¹)))))

  identity-lift = equiv-lift (identityComparison-isEquiv D) inverted-identity

  object : MAP All.maps (Core D)
  object = FunctorLift.lift identity-lift

  object-comparison : (constantMap D ∘ object) =₁ All.inclusion
  object-comparison = inverted-identity-comparison ∙
    ((π ◁ FunctorLift.comparison identity-lift) ∙
      (comp-assoc object (identityComparison D) π ∙
        (identityComparison-over-morphisms D ⁻¹ ▷ object)))

  constantMap-isEmbedding = embedding-cong (identityComparison-over-morphisms D)
    (LeftCancellation.compose (identityComparison D) π (isomorphismInclusion-isEmbedding D)
      (equivalence-isEmbedding _ (identityComparison-isEquiv D)))

  abstract
    constants-isEquiv : IsEquiv constants
    constants-isEquiv = record
      { inverse = object
      ; sectionIso = embedding-reflect (constantMap D) constantMap-isEmbedding _ _
          (comp-assoc constants object (constantMap D) ∙
            ((object-comparison ▷ constants) ⁻¹ ∙
              (constants-comparison ⁻¹ ∙ comp-unitʳ (constantMap D))))
      ; retractionIso = embedding-reflect All.inclusion All.inclusion-isEmbedding _ _
          (comp-assoc object constants All.inclusion ∙
            ((constants-comparison ▷ object) ⁻¹ ∙
              (object-comparison ⁻¹ ∙ comp-unitʳ All.inclusion))) }
```
