# The collection of isomorphisms

The collection in `lem:Collection_of_Isomorphisms` is the core of `Iso C`,
with its canonical map to the mapping anima of arrows. The core of the
functor category supplies the comparison with `Map [1] C`. Rezk identifies
this collection with the core of `C`, compatibly with constant arrows.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section01.IsomorphismCollections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E using (Iso; isoArrow)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I using (identityArrow)
open import SCT.VolumeI.Chapter02.Section03.IsomorphismEmbedding 𝒯 M ℱ P I E S Q using (isoArrow-isEmbedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; equivalence-isEmbedding; module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P using (map-preserves-embedding)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (MorphismCollection)

isomorphismInclusion : (C : CAT) → MAP (Core (Iso C)) (Map [1] C)
isomorphismInclusion C = CoreOfFun.uncurrying [1] C ∘ mapPost isoArrow

abstract
  isomorphismInclusion-isEmbedding : (C : CAT) → IsEmbedding (isomorphismInclusion C)
  isomorphismInclusion-isEmbedding C = LeftCancellation.compose (mapPost isoArrow)
    (CoreOfFun.uncurrying [1] C)
    (equivalence-isEmbedding _ (CoreOfFun.uncurrying-isEquiv [1] C))
    (map-preserves-embedding One isoArrow (isoArrow-isEmbedding C))

isomorphisms : (C : CAT) → MorphismCollection C
isomorphisms C = record
  { collection = Core (Iso C) ; collection-isAn = core-isAn (Iso C)
  ; inclusion = isomorphismInclusion C ; inclusion-isEmbedding = isomorphismInclusion-isEmbedding C }

constantMap : (C : CAT) → MAP (Core C) (Map [1] C)
constantMap C = mapPre (terminate [1])

constantMap-evaluation : (C : CAT) → mapUncurry (constantMap C) =₁ (coreInclusion C ∘ pr₁)
constantMap-evaluation C = (comp-assoc pr₁ (product-unitʳ-inverse (Core C)) mapEval) ⁻¹ ∙
  ((mapEval ◁ (pair-pre (id (Core C)) (terminate (Core C)) pr₁) ⁻¹) ∙
    ((mapEval ◁ pair-cong (idIso (id (Core C) ∘ pr₁))
      (terminal-iso (terminate [1] ∘ pr₂) (terminate (Core C) ∘ pr₁))) ∙
      mapPre-β (terminate [1])))

core-constant : (C : CAT) →
  (CoreOfFun.uncurrying [1] C ∘ mapPost {C = One} (identityArrow {C})) =₁ constantMap C
core-constant C = mapReflect (core-isAn C) _ _
  ((constantMap-evaluation C) ⁻¹ ∙
    (pair-β₁ (coreInclusion C ∘ pr₁) (id [1] ∘ pr₂) ∙
      ((funCurry-β pr₁ ▷ productMap (coreInclusion C) (id [1])) ∙
        (funUncurry-restrict identityArrow (coreInclusion C) ∙
          (funUncurry-cong (coreInclusion-natural identityArrow) ∙
            ((funUncurry-restrict (coreInclusion (Fun [1] C)) (mapPost identityArrow)) ⁻¹ ∙
              ((CoreOfFun.uncurrying-evaluation [1] C ▷ productMap (mapPost identityArrow) (id [1])) ∙
                mapUncurry-restrict (CoreOfFun.uncurrying [1] C) (mapPost identityArrow))))))))

module WithRezk (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where
  open Rezk 𝒯 M ℱ P I E using (identityIso; identityIso-arrow)
  open Rezk.RezkAxiom R

  identityComparison : (C : CAT) → MAP (Core C) (Core (Iso C))
  identityComparison C = mapPost identityIso

  identityComparison-isEquiv : (C : CAT) → IsEquiv (identityComparison C)
  identityComparison-isEquiv C = mapPost-isEquiv identityIso (rezk-isEquiv C)

  identityComparison-over-morphisms : (C : CAT) →
    (isomorphismInclusion C ∘ identityComparison C) =₁ constantMap C
  identityComparison-over-morphisms C = core-constant C ∙
    ((CoreOfFun.uncurrying [1] C ◁ mapPost-cong identityIso-arrow) ∙
      ((CoreOfFun.uncurrying [1] C ◁ mapPost-comp identityIso isoArrow) ∙
        comp-assoc (mapPost identityIso) (mapPost isoArrow) (CoreOfFun.uncurrying [1] C)))
```
