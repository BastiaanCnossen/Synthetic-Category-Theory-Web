# Isomorphisms embed into arrows

This is `lem:Isomorphisms_Embed_Into_All_Morphisms`, before Rezk.
Composition with the universal invertible arrow is an equivalence on
either side. Pulling back at the identity arrows makes the categories of
one-sided inverse triangles unique. The rearrangement of the raw defining
pullbacks combines those two conditions, and hence makes the projection
from its self-pullback an equivalence.

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

module SCT.VolumeI.Chapter02.Section03.IsomorphismEmbedding
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.OneSidedInverseFibers 𝒯 M ℱ P I E S Q
open import SCT.VolumeI.Chapter02.Section03.PullbackCalculus.InversePullbackComparison 𝒯 M ℱ P I E
  using (module InverseComparison)
open import SCT.VolumeI.Chapter02.Section03.PullbackCalculus.IntersectionEmbedding 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P

isoArrow-isEmbedding : (C : CAT) → IsEmbedding (isoArrow {C})
isoArrow-isEmbedding C = embedding-cong Rearrange.comparison-arrow
  (Both.embedding
    (change-right-projection rightInverseArrow Rearrange.comparison-arrow Fibers.right-inverse-projection-isEquiv)
    (change-right-projection leftInverseArrow Rearrange.comparison-arrow Fibers.left-inverse-projection-isEquiv))
  where
  module Rearrange = InverseComparison C
  module Fibers = UniversalFibers C
  module Both = Intersection rightInverseArrow leftInverseArrow Rearrange.square Rearrange.square-isPullback

module WithRezk (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where
  open Rezk 𝒯 M ℱ P I E using (identityIso; identityIso-arrow)
  open Rezk.RezkAxiom R

  identityArrow-isEmbedding : (C : CAT) → IsEmbedding (identityArrow {C})
  identityArrow-isEmbedding C = embedding-cong identityIso-arrow
    (LeftCancellation.compose identityIso isoArrow (isoArrow-isEmbedding C)
      (equivalence-isEmbedding identityIso (rezk-isEquiv C)))
```

The final statement is `cor:Inclusion_Into_Arrow_Category_Embedding`.
Only this corollary uses the Rezk axiom.
