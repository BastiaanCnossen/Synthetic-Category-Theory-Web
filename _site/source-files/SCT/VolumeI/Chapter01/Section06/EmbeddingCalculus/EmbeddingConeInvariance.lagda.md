# Pullback cones along an embedding

When the right leg of a cospan is an embedding, the first projection of
its pullback is an embedding. Thus two cones with identified first legs
have identified comparison functors. In particular, either comparison
is an equivalence if the other is. This argument does not equate their
chosen commutativity identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingConeInvariance
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)

abstract
  pullback-embedding-invariant : {C D E X : CAT} {f : MAP C E} {g : MAP D E} →
    IsEmbedding g → (s t : Cone f g X) → Cone.left s =₁ Cone.left t →
    IsPullback s → IsPullback t
  pullback-embedding-invariant {f = f} {g} eg s t α es = equiv-transport comparison es
    where
    comparison : pullbackLift s =₁ pullbackLift t
    comparison = embedding-reflect pullback₁ (chosen-base-change-embedding f g eg) _ _
      ((pullbackLift-β₁ t) ⁻¹ ∙ (α ∙ pullbackLift-β₁ s))


module ChangeRight {C D D′ E X : CAT} {f : MAP C E} {g : MAP D E} {g′ : MAP D′ E}
  (u : MAP D D′) (eu : IsEquiv u) (θ : (g′ ∘ u) =₁ g)
  (eg′ : IsEmbedding g′) (s : Cone f g X) (t : Cone f g′ X)
  (α : Cone.left s =₁ Cone.left t) (et : IsPullback t) where
  cospan : CospanMap f g f g′
  cospan = record { left = id C ; right = u ; base = id E
    ; leftSquare = (comp-unitˡ f) ⁻¹ ∙ comp-unitʳ f
    ; rightSquare = (comp-unitˡ g) ⁻¹ ∙ θ }
  module Change = CospanMap cospan using (pullbackMap; pullbackMap-β)
  module Equivalence = CospanEquivalence cospan (id-isEquiv C) eu (id-isEquiv E)
    using (pullbackMap-isEquiv)
  H = Change.pullbackMap
  abstract
    first : (pullback₁ {f = f} {g′} ∘ H) =₁ pullback₁ {f = f} {g}
    first = comp-unitˡ pullback₁ ∙ ConeIso.leftIso Change.pullbackMap-β
    comparison : (H ∘ pullbackLift s) =₁ pullbackLift t
    comparison = embedding-reflect pullback₁ (chosen-base-change-embedding f g′ eg′) _ _
      ((pullbackLift-β₁ t) ⁻¹ ∙ (α ∙ (pullbackLift-β₁ s ∙
        ((first ▷ pullbackLift s) ∙ (comp-assoc (pullbackLift s) H pullback₁) ⁻¹))))
    source-isPullback : IsPullback s
    source-isPullback = equiv-cancel-left (pullbackLift s) H Equivalence.pullbackMap-isEquiv
      (equiv-transport (comparison ⁻¹) et)
```
