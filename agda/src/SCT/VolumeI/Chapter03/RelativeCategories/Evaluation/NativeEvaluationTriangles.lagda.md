# Evaluation of a triangle between functor categories

The triangle obtained by uncurrying factors as product with the
argument category, followed by evaluation. The computation below
retains the structure triangle, including its inverse comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.NativeEvaluationTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; pre-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P using (triangle-identification)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedTriangles 𝒯 M ℱ P using (module Uncurry)

module Evaluation (K : CAT) {C S : CAT} (f : MAP C S) where
  basic : FunctorOver (funUncurry (funPost {C = K} f)) f
  basic = record { lift = funEval ; comparison = (funPost-β f) ⁻¹ }

  module Factor {X : CAT} {k : MAP X (Fun K S)} (v : FunctorOver k (funPost f)) where
    h = FunctorLift.lift v
    H = productMap h (id K)
    θ = funUncurryIso (FunctorLift.comparison v)
    ρ = funUncurry-restrict (funPost f) h
    β = funPost-β f ▷ H
    A = comp-assoc H funEval f
    source = compose-over basic (Uncurry.value K S v)
    target = Triangle.value f k v
    abstract
      inverse-post : (funPost-uncurry f h) ⁻¹ =₂ (ρ ⁻¹ ∙ (β ⁻¹ ∙ A ⁻¹))
      inverse-post = isoComp-assoc-at (ρ ⁻¹) (β ⁻¹) (A ⁻¹) ∙
        (isoComp-cong (inverse-composite β ρ) (idIso (A ⁻¹)) ∙
          inverse-composite A (β ∙ ρ))
      triangle : FunctorLift.comparison source =₂ FunctorLift.comparison target
      triangle = isoComp-cong (idIso θ) (inverse-post ⁻¹) ∙
        (isoComp-assoc-at θ (ρ ⁻¹) (β ⁻¹ ∙ A ⁻¹) ∙
          isoComp-cong (idIso (θ ∙ ρ ⁻¹))
            (isoComp-cong (pre-inverse (funPost-β f) H) (idIso (A ⁻¹))))
      comparison : FunctorOverIso source target
      comparison = triangle-identification _ _ _ triangle
      comparison-underlying : FunctorOverIso.underlying comparison =₂ idIso (funUncurry h)
      comparison-underlying = idIso _
```
