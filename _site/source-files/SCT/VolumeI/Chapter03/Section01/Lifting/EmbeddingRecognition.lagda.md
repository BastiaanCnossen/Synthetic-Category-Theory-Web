# Recognizing embeddings by specified lifts

Conversely to `EmbeddingLifting`, lifting every identification with its
specified image makes the diagonal universal. Apply the lifting property
to the matching of the self-pullback. The first leg supplies the inverse
to the diagonal, and its two leg comparisons retain that matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingRecognition
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (IsEmbedding; diagonalCone)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P using (cone-isPullback-from-lifting)

module Criterion {C D : CAT} (f : MAP C D)
  (lifting : {X : CAT} (h k : MAP X C) (α : (f ∘ h) =₁ (f ∘ k)) →
    FunctorLift (postWhisker f) α) where
  h : MAP (Pullback f f) C
  h = pullback₁
  k : MAP (Pullback f f) C
  k = pullback₂
  τ : (f ∘ h) =₁ (f ∘ k)
  τ = pullbackMatch
  α : h =₁ k
  α = FunctorLift.lift (lifting h k τ)
  assoc = comp-assoc h (id C) f
  δ = comp-unitˡ h
  β = α ∙ δ

  abstract
    diagonal-matching : Cone.match (conePre h (diagonalCone f)) =₂ idIso (f ∘ (id C ∘ h))
    diagonal-matching = isoComp-inverseʳ-at assoc ∙ isoComp-cong (idIso assoc)
      (isoComp-unitˡ-at (assoc ⁻¹) ∙ isoComp-cong (preWhisker-idIso (f ∘ id C) h) (idIso (assoc ⁻¹)))

    matching : (τ ∙ (f ◁ δ)) =₂ ((f ◁ β) ∙ Cone.match (conePre h (diagonalCone f)))
    matching = isoComp-cong (idIso (f ◁ β)) (diagonal-matching ⁻¹) ∙
      ((isoComp-unitʳ-at (f ◁ β)) ⁻¹ ∙
        ((postWhisker-isoComp-at f α δ) ⁻¹ ∙
          isoComp-cong ((FunctorLift.comparison (lifting h k τ)) ⁻¹) (idIso (f ◁ δ))))

  comparison : ConeIso (conePre h (diagonalCone f)) (pullbackCone f f)
  comparison = record { leftIso = δ ; rightIso = β ; compatible = matching }

  abstract
    isEmbedding : IsEmbedding f
    isEmbedding = cone-isPullback-from-lifting (diagonalCone f) h comparison
      (λ u v Φ → comp-unitˡ v ∙ (ConeIso.leftIso Φ ∙ (comp-unitˡ u) ⁻¹))
```
