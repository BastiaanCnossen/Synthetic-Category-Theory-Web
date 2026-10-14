# Characterizations of embeddings

The diagonal criterion uses the direct diagonal-pullback cone. Changing its
right leg by the unitor gives the stated square with legs the diagonal and
the original functor. Its complete cone comparison transfers universality
in both directions.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (cone-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.Embeddings using (IsEmbedding; diagonal-cone; embedding-projection-isEquiv; embedding-from-projection-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.DiagonalPullbacks using (module DiagonalPullback)

open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-transport; equiv-compose; equiv-cancel-right)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPost; mapPost-isEquiv)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection using (post-tests-all)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks using (mapped-cone; module MappingPullback)

module _ {Γ : Context} where
  module DiagonalCharacterization {C D : CAT Γ} (f : MAP C D) where
    private
      module Description = DiagonalPullback f f
      module Square = Description.Square (diagonal-cone f)

    square : Cone (productMap f f) (pair (id D) (id D)) C
    square = cone-change-legs Square.value (pair (id C) (id C)) f
      (id₌ (pair (id C) (id C))) (comp-unitʳ f)

    cone-law : ConeIdentification₁ Square.value square
    cone-law = cone-change-legs-β Square.value (pair (id C) (id C)) f
      (id₌ (pair (id C) (id C))) (comp-unitʳ f)

    from-embedding : IsEmbedding f → IsPullback square
    from-embedding ef = isPullback-cone-identification cone-law (Square.preserve ef)

    to-embedding : IsPullback square → IsEmbedding f
    to-embedding es = Square.reflect (isPullback-cone-identification (cone-inverse cone-law) es)
```

## Mapping tests

Mapping out of each categorical test object preserves and detects the
projection criterion. The factorization of the actual mapped cone identifies
its first projection with postcomposition by the original first projection.
No anima restriction is placed on the test category.

```agda
  map-preserves-embedding : {C D : CAT Γ} (T : CAT Γ) (f : MAP C D)
    → IsEmbedding f → IsEmbedding (mapPost {C = T} f)
  map-preserves-embedding T f ef = embedding-from-projection-isEquiv (mapPost f)
    (equiv-cancel-right (pullback-factor (mapped-cone T (pullback-cone f f))) pullback₁
      (MappingPullback.square-isPullback T f f)
      (equiv-transport ((pullback-factor-β₁ (mapped-cone T (pullback-cone f f))) ⁻¹)
        (mapPost-isEquiv pullback₁ (embedding-projection-isEquiv f ef))))

  map-detects-embedding : {C D : CAT Γ} (f : MAP C D)
    → ((T : CAT Γ) → IsEmbedding (mapPost {C = T} f)) → IsEmbedding f
  map-detects-embedding f tests = embedding-from-projection-isEquiv f (post-tests-all pullback₁ (λ T →
    equiv-transport (pullback-factor-β₁ (mapped-cone T (pullback-cone f f)))
      (equiv-compose (pullback-factor (mapped-cone T (pullback-cone f f))) pullback₁
        (MappingPullback.square-isPullback T f f) (embedding-projection-isEquiv (mapPost f) (tests T)))))
```
