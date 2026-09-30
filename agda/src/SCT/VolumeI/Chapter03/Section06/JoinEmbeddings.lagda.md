# The boundary of a join is an embedding

The interval boundary is the core inclusion after an equivalence.
Products preserve embeddings, and the join boundary is its specified
pullback. This supplies the embedding assertion in `prop:core_of_join`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter02.Section01.IntervalCore as IntervalCore
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.JoinEmbeddings
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (K : IntervalCore.IntervalCoreAxiom 𝒯 M B I)
  (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (A : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R)
  (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (coreInclusion)
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-cong; equivalence-isEmbedding; module LeftCancellation; base-change-embedding)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter02.Section05.PullbackAnimae 𝒯 M ℱ P I E S Q R A using (coreInclusion-isEmbedding)
open import SCT.VolumeI.Chapter03.Section02.Factorization.ProductEmbeddings 𝒯 P using (product-second-isEmbedding)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I using (boundary)
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary 𝒯 M B P U I using (weakened-boundary)
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.BoundaryCore 𝒯 M B P U I K using (boundary-comparison)
open IntervalCore 𝒯 M B I using (intervalCore)
open IntervalCore.IntervalCoreAxiom K
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J

abstract
  boundary-isEmbedding : IsEmbedding boundary
  boundary-isEmbedding = embedding-cong boundary-comparison
    (LeftCancellation.compose intervalCore (coreInclusion [1]) (coreInclusion-isEmbedding [1])
      (equivalence-isEmbedding intervalCore intervalCore-isEquiv))

  weakened-boundary-isEmbedding : (Γ : CAT) → IsEmbedding (weakened-boundary Γ)
  weakened-boundary-isEmbedding Γ = product-second-isEmbedding Γ boundary boundary-isEmbedding

  inclusion-isEmbedding : {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) → IsEmbedding (inclusion p q)
  inclusion-isEmbedding {Γ = Γ} p q = base-change-embedding BoundaryPullback.cone
    (boundary-isEquiv p q) (weakened-boundary-isEmbedding Γ)
    where
    module BoundaryPullback = BoundaryComparison dataJoin p q
```
