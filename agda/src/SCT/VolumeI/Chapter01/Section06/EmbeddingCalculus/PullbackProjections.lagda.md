# Recognizing a pullback of embeddings

For a square whose two parallel legs are embeddings, existence of the
required factorization suffices. The chosen pullback comparison is then
an embedding with a section. This is the same argument used for
pullback cancellation along embeddings in Chapter 1.

The input remains a specified cone. Its matching is used in the
comparison functor; no uniqueness of arbitrary coherence witnesses is
assumed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PullbackProjections
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P

embedding-pullback : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → IsEmbedding g → IsEmbedding (Cone.left s) →
  FunctorLift (Cone.left s) (pullback₁ {f = f} {g}) → IsPullback s
embedding-pullback {f = f} {g} s eg eu factor =
  embedding-with-section comparison comparison-embedding section section-law
  where
  comparison = pullbackLift s
  p = pullback₁ {f = f} {g}
  section = FunctorLift.lift factor
  projection-isEmbedding = chosen-base-change-embedding f g eg
  comparison-embedding = LeftCancellation.cancel comparison p projection-isEmbedding
    (embedding-cong ((pullbackLift-β₁ s) ⁻¹) eu)
  section-law : (comparison ∘ section) =₁ id (Pullback f g)
  section-law = embedding-reflect p projection-isEmbedding _ _
    ((comp-unitʳ p) ⁻¹ ∙
      (FunctorLift.comparison factor ∙ ((pullbackLift-β₁ s ▷ section) ∙
        (comp-assoc section comparison p) ⁻¹)))
```
