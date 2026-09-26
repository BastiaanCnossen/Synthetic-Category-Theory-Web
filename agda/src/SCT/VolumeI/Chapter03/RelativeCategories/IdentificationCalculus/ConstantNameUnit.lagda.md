# The constant-name comparison at the terminal parameter

At the identity parameter, the constant-name normalization is the curry
beta comparison followed by the uncurried right unitor. Restricting this
identity along the terminal insertion gives its decoding form.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameRestriction as ConstantRestriction
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.PostNamingCoherence as PostNaming
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.PointReductionCoherence as PointReduction
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as PFU

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameUnit
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in; oneProduct-retraction)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate 𝒯 M using (parameter-over)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.EvaluationUnitCoherence 𝒯 M ℱ
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingIdentifications 𝒯 M ℱ
open Structural vocabulary terminal products productLaws composition whiskering using (preWhisker-id-at)
open PFU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (productMap-id-triangle₂)

module Unit {C S : CAT} (f : MAP C S) where
  F : MAP One (Fun C S)
  F = nameFun f
  A : MAP (One × C) S
  A = funUncurry F
  q : MAP (One × C) S
  q = f ∘ pr₂
  J : MAP (One × C) (One × C)
  J = productMap (id One) (id C)
  d : J =₁ id (One × C)
  d = productMap-id One C
  β : A =₁ q
  β = funCurry-β q
  ρ : (F ∘ id One) =₁ F
  ρ = comp-unitʳ F
  i : MAP C (One × C)
  i = oneProduct-in C
  module Reduce = PointReduction.Reduction 𝒯 i (pr₂ {C = One}) (oneProduct-retraction C)

  abstract
    projection-comparison : parameter-over (id One) f =₂ unit-at-product q
    projection-comparison = (PostUnit.comparison (pr₂ {C = One}) f) ⁻¹ ∙
      isoComp-cong ((postWhisker f ◁ productMap-id-triangle₂ One C) ⁻¹)
        (idIso (comp-assoc J (pr₂ {C = One}) f))

    beta-unit : (unit-at-product q ∙ (β ▷ J)) =₂ (β ∙ unit-at-product A)
    beta-unit = isoComp-assoc-at β (comp-unitʳ A) (A ◁ d) ∙
      (isoComp-cong (preWhisker-id-at β) (idIso (A ◁ d)) ∙
        ((isoComp-assoc-at (comp-unitʳ q) (β ▷ id (One × C)) (A ◁ d)) ⁻¹ ∙
          (isoComp-cong (idIso (comp-unitʳ q)) ((interchange-at β d) ⁻¹) ∙
            isoComp-assoc-at (comp-unitʳ q) (q ◁ d) (β ▷ J))))

    comparison : uncurry-constant-name f (id One) =₂ (β ∙ funUncurryIso ρ)
    comparison = isoComp-cong (idIso β) ((UncurryUnit.comparison F) ⁻¹) ∙
      (isoComp-assoc-at β (unit-at-product A) (funUncurry-restrict F (id One)) ∙
        (isoComp-cong (beta-unit ∙ isoComp-cong projection-comparison (idIso (β ▷ J)))
          (idIso (funUncurry-restrict F (id One))) ∙
          (ConstantRestriction.Restriction.normalize 𝒯 M ℱ P f (id One) (id One) (id One)) ⁻¹))

    decoded : (Reduce.reduce f ∙ (uncurry-constant-name f (id One) ▷ i)) =₂
      (decode-nameFun f ∙ decodeFunIso ρ)
    decoded = isoComp-cong (PostNaming.Normalization.name-normal 𝒯 M ℱ (id S) f f)
        ((decodeFunIso-at ρ) ⁻¹) ∙
      ((isoComp-assoc-at (Reduce.reduce f) (β ▷ i) (funUncurryIso ρ ▷ i)) ⁻¹ ∙
        isoComp-cong (idIso (Reduce.reduce f))
          (preWhisker-isoComp-at β (funUncurryIso ρ) i ∙ (preWhisker i ◁ comparison)))
```
