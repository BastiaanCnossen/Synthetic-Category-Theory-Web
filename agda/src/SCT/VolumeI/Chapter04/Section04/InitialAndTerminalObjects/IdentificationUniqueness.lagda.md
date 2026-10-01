# Uniqueness of identifications at universal objects

Identifications into a terminal object, or out of an initial object, are
unique. Rezk and the embedding of identity arrows let us reflect the full
comparison of their constant morphism expressions. This includes the
source and target equations, rather than only the underlying arrows.

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

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.IdentificationUniqueness
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.UniversalComparisons 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows 𝒯 M ℱ I
  using (constant-identification; constant-frame; constant-frame-natural)
import SCT.VolumeI.Chapter02.Section03.IsomorphismEmbedding as Embedding
open Embedding.WithRezk 𝒯 M ℱ P I E S Q R using (identityArrow-isEmbedding)
open import SCT.VolumeI.Chapter03.Section01.Lifting.EmbeddingLifting 𝒯 P using (embedding-lift)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)

module Reflection {Γ C : CAT} {x y : MAP Γ C} (α β : x =₁ y)
  (w : ExpressionIso (constant-identification α) (constant-identification β)) where
  private
    module W = ExpressionIso w
    lifted = embedding-lift identityArrow (identityArrow-isEmbedding C) x x W.comparison
    δ = FunctorLift.lift lifted
    image = FunctorLift.comparison lifted
    source-frame = constant-frame ev₀ identity-source x
    target-frame = constant-frame ev₁ identity-target x

  abstract
    reflected-identity : δ =₂ idIso x
    reflected-identity = cancel-right-reflect source-frame
      ((isoComp-unitˡ-at source-frame) ⁻¹ ∙
        (W.source-compatible ∙
          (isoComp-cong (idIso source-frame) (postWhisker ev₀ ◁ image) ∙
            (constant-frame-natural ev₀ identity-source δ) ⁻¹)))

    comparison-identity : W.comparison =₂ idIso (identityArrow ∘ x)
    comparison-identity = postWhisker-idIso identityArrow x ∙
      ((postWhisker identityArrow ◁ reflected-identity) ∙ image ⁻¹)

    comparison : α =₂ β
    comparison = (cancel-right-reflect target-frame
      (W.target-compatible ∙
        (isoComp-unitʳ-at (β ∙ target-frame) ∙
          isoComp-cong (idIso (β ∙ target-frame))
            (postWhisker-idIso ev₁ (identityArrow ∘ x) ∙
              (postWhisker ev₁ ◁ comparison-identity))) ⁻¹)) ⁻¹

constant-identification-reflect : {Γ C : CAT} {x y : MAP Γ C} (α β : x =₁ y) →
  ExpressionIso (constant-identification α) (constant-identification β) → α =₂ β
constant-identification-reflect = Reflection.comparison

abstract
  terminal-identifications : {Γ C : CAT} (t : Obj-abs C) (et : IsTerminal t)
    {x : MAP Γ C} (α β : x =₁ const t) → α =₂ β
  terminal-identifications t et {x} α β = constant-identification-reflect α β
    (terminal-comparison t et x (constant-identification α) (constant-identification β))

  initial-identifications : {Γ C : CAT} (z : Obj-abs C) (ez : IsInitial z)
    {y : MAP Γ C} (α β : const z =₁ y) → α =₂ β
  initial-identifications z ez {y} α β = constant-identification-reflect α β
    (initial-comparison z ez y (constant-identification α) (constant-identification β))

  terminal-Iso₂ : {C : CAT} (t : Obj-abs C) (et : IsTerminal t)
    {x y : Obj-abs C} (τ : y =₁ t) (α β : x =₁ y) → α =₂ β
  terminal-Iso₂ t et τ α β = cancel-left-reflect ((const-One t) ⁻¹ ∙ τ)
    (terminal-identifications t et (((const-One t) ⁻¹ ∙ τ) ∙ α) (((const-One t) ⁻¹ ∙ τ) ∙ β))

  initial-Iso₂ : {C : CAT} (z : Obj-abs C) (ez : IsInitial z)
    {x y : Obj-abs C} (σ : z =₁ x) (α β : x =₁ y) → α =₂ β
  initial-Iso₂ z ez σ α β = cancel-right-reflect (σ ∙ const-One z)
    (initial-identifications z ez (α ∙ (σ ∙ const-One z)) (β ∙ (σ ∙ const-One z)))
```
