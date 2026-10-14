# Lifting a specified identification through an embedding

The generic lifting theorem now lives with the Chapter 1 pullback and
embedding calculus. This entry preserves the Chapter 3 interface, including
the specified image of each lifted identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingLifting
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PrescribedLifting 𝒯 P
  public using (module Lift)
import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PrescribedLifting as Generic

embedding-lift : {A B Γ : CAT} (f : MAP A B) → IsEmbedding f →
  (h k : MAP Γ A) (α : (f ∘ h) =₁ (f ∘ k)) → FunctorLift (postWhisker f) α
embedding-lift = Generic.embedding-lift 𝒯 P
```
