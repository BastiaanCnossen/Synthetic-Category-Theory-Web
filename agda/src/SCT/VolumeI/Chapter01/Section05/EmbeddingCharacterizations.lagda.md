# The mapping and diagonal characterizations of embeddings

The mapping criterion uses the equivalent projection criterion for an
embedding, so no coherence for a separately chosen mapping of the diagonal
is assumed. The second criterion specializes the constructed diagonal
description of pullbacks, retaining its matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.EmbeddingCharacterizations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯 M
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeCalculus 𝒯 using (coneRetarget; coneRetarget-β; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section05.Embeddings 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.MappingPullbacks 𝒯 M P using (module MappingPullback; mappedCone)
open import SCT.VolumeI.Chapter01.Section05.DiagonalPullbacks 𝒯 P using (module DiagonalPullback)
open import SCT.VolumeI.Chapter01.Section03.EquivalenceDetection 𝒯 M using (post-tests-all)

map-preserves-embedding : {C D : CAT} (T : CAT) (f : MAP C D) →
  IsEmbedding f → IsEmbedding (mapPost {C = T} f)
map-preserves-embedding T f ef = projection-embedding (mapPost f)
  (equiv-cancel-right (pbLift (mappedCone T (pbCone f f))) pb₁ (MappingPullback.square-isPullback T f f)
    (equiv-transport (invIso (pbLift-β₁ (mappedCone T (pbCone f f))))
      (mapPost-isEquiv pb₁ (embedding-projection f ef))))

map-detects-embedding : {C D : CAT} (f : MAP C D) →
  ((T : CAT) → IsEmbedding (mapPost {C = T} f)) → IsEmbedding f
map-detects-embedding f tests = projection-embedding f (post-tests-all pb₁ (λ T →
  equiv-transport (pbLift-β₁ (mappedCone T (pbCone f f)))
    (equiv-compose (pbLift (mappedCone T (pbCone f f))) pb₁
      (MappingPullback.square-isPullback T f f) (embedding-projection (mapPost f) (tests T)))))

module DiagonalCharacterization {C D : CAT} (f : MAP C D) where
  module Description = DiagonalPullback f f
  module Square = Description.Square (diagonalCone f)

  square : Cone (productMap f f) (pair (id D) (id D)) C
  square = coneRetarget Square.value (pair (id C) (id C)) f
    (idIso (pair (id C) (id C))) (comp-unitʳ f)
  comparison = coneRetarget-β Square.value (pair (id C) (id C)) f
    (idIso (pair (id C) (id C))) (comp-unitʳ f)

  from-embedding : IsEmbedding f → IsPullback square
  from-embedding ef = pullback-cone-invariant comparison (Square.preserve ef)
  to-embedding : IsPullback square → IsEmbedding f
  to-embedding es = Square.reflect (pullback-cone-invariant (coneIso-inverse comparison) es)
```
