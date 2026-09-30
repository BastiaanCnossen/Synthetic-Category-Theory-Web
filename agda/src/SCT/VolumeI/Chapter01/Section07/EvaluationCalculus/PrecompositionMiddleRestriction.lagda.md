# Restricting the common precomposition middle

The middle frame agrees with restriction of the opposite component
followed by the identified evaluator. This is the exact shared-frame
comparison needed for the two triangle legs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionMiddleRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionMiddleEvaluation as Middle
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedSeparationChange as Change
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunPrecompositionCompositeImage as Composite

module At {C D : CAT} (K : CAT) (l : MAP C D) (r : MAP D C) where
  module Original = Middle.At 𝒯 M ℱ P K l r
  module F = Original.F
  module Lifted = Composite.CompositorImage 𝒯 M ℱ P r l F.L
  σ : MAP (F.X × D) (F.Y × D)
  σ = productMap F.L (id D)
  d : MAP (F.Y × D) K
  d = funEval
  j : MAP (F.X × D) (F.X × D)
  j = productMap (id F.X) (l ∘ r)
  z : MAP (F.X × D) (F.X × D)
  z = pair pr₁ (l ∘ (r ∘ pr₂))
  k : MAP (F.Y × D) (F.Y × D)
  k = productMap (id F.Y) (l ∘ r)
  v : MAP (F.Y × D) (F.Y × D)
  v = pair pr₁ (l ∘ (r ∘ pr₂))
  δ : j =₁ z
  δ = pair-cong (comp-unitˡ pr₁) (comp-assoc pr₂ r l)
  ε : k =₁ v
  ε = pair-cong (comp-unitˡ pr₁) (comp-assoc pr₂ r l)
  separation : (k ∘ σ) =₁ (σ ∘ j)
  separation = productMap-separate F.L (l ∘ r)
  ν : (v ∘ σ) =₁ (σ ∘ z)
  ν = (σ ◁ δ) ∙ (separation ∙ (ε ⁻¹ ▷ σ))
  χ = Original.ProductFrame.Triple.Right.χ
  counit-frame : funUncurry (F.L ∘ F.R) =₁ (d ∘ v)
  counit-frame = (d ◁ ε) ∙ Lifted.leading
  Q : funUncurry ((F.L ∘ F.R) ∘ F.L) =₁ (funUncurry (F.L ∘ F.R) ∘ σ)
  Q = funUncurry-restrict (F.L ∘ F.R) F.L

  abstract
    square : (ν ∙ (ε ▷ σ)) =₂ ((σ ◁ δ) ∙ separation)
    square = cancel-inverse-tail ((σ ◁ δ) ∙ separation) (ε ▷ σ) ∙
      isoComp-cong
        (isoComp-cong (idIso ((σ ◁ δ) ∙ separation)) (pre-inverse ε σ) ∙
          (isoComp-assoc-at (σ ◁ δ) separation (ε ⁻¹ ▷ σ)) ⁻¹)
        (idIso (ε ▷ σ))

  module SeparationResult = Change.At 𝒯 σ j z k v δ ε separation ν square d F.W F.e Original.β χ

  abstract
    value : F.middle =₂ (SeparationResult.Ξ ∙ ((counit-frame ▷ σ) ∙ Q))
    value = isoComp-assoc-at SeparationResult.Ξ (counit-frame ▷ σ) Q ∙
      isoComp-cong (SeparationResult.append Lifted.leading) (idIso Q) ∙
      (isoComp-assoc-at SeparationResult.n (SeparationResult.prefix ∙ (Lifted.leading ▷ σ)) Q) ⁻¹ ∙
      isoComp-cong (idIso SeparationResult.n)
        ((isoComp-assoc-at SeparationResult.prefix (Lifted.leading ▷ σ) Q) ⁻¹) ∙
      isoComp-cong (idIso SeparationResult.n) Lifted.law ∙ Original.value
```
