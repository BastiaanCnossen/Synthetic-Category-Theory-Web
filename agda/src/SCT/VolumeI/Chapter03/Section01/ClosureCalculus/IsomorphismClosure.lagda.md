# Isomorphisms are closed under composition

This completes `lem:Collection_of_Isomorphisms`. By Rezk and recognition,
the isomorphism collection is the morphism image of the embedded core.
The comparison uses the actual core of `Iso C` and its inclusion.
Closure follows by lifting triangles through that embedding.

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

import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

module SCT.VolumeI.Chapter03.Section01.ClosureCalculus.IsomorphismClosure
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I using (identityArrow)
open Recognition.RecognitionAxiom N using (anima-isGroupoid)
open import SCT.VolumeI.Chapter02.Section05.PullbackAnimae 𝒯 M ℱ P I E S Q R N
  using (coreInclusion-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M using (mapPre-mapPost)
open import SCT.VolumeI.Chapter01.Section03.FactorizationCalculus
  vocabulary terminal products productLaws composition
  using (lift-from-equivalent-source)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
open WithRezk R
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.CompositionClosure 𝒯 M ℱ P I E S using (ClosedUnderComposition)
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.EmbeddingImageClosure 𝒯 M ℱ P I E S
  using () renaming (module Closure to ImageClosure)

module At (C : CAT) where
  core-arrows = mapPost {C = [1]} (coreInclusion C)
  constant = constantMap (Core C)
  isomorphism = identityComparison C ∘ mapPost {C = One} (coreInclusion C)

  constant-isEquiv : IsEquiv constant
  constant-isEquiv = equiv-transport (core-constant (Core C))
    (equiv-compose (mapPost identityArrow) (CoreOfFun.uncurrying [1] (Core C))
      (mapPost-isEquiv identityArrow (anima-isGroupoid (core-isAn C)))
      (CoreOfFun.uncurrying-isEquiv [1] (Core C)))

  isomorphism-isEquiv : IsEquiv isomorphism
  isomorphism-isEquiv = equiv-compose (mapPost (coreInclusion C)) (identityComparison C)
    (core-universal One C one-isAn) (identityComparison-isEquiv C)

  square : (core-arrows ∘ constant) =₁ (isomorphismInclusion C ∘ isomorphism)
  square = comp-assoc (mapPost (coreInclusion C)) (identityComparison C) (isomorphismInclusion C) ∙
    (((identityComparison-over-morphisms C) ⁻¹ ▷ mapPost (coreInclusion C)) ∙
      (mapPre-mapPost (terminate [1]) (coreInclusion C)) ⁻¹)

  from-core-arrows : FunctorLift (isomorphismInclusion C) core-arrows
  from-core-arrows = lift-from-equivalent-source core-arrows (isomorphismInclusion C)
    constant isomorphism constant-isEquiv square

  to-core-arrows : FunctorLift core-arrows (isomorphismInclusion C)
  to-core-arrows = lift-from-equivalent-source (isomorphismInclusion C) core-arrows
    isomorphism constant isomorphism-isEquiv (square ⁻¹)

  closed : ClosedUnderComposition (isomorphisms C)
  closed = ImageClosure.closed (coreInclusion C) (coreInclusion-isEmbedding C)
    (isomorphisms C) to-core-arrows from-core-arrows

isomorphisms-closed : (C : CAT) → ClosedUnderComposition (isomorphisms C)
isomorphisms-closed = At.closed
```
