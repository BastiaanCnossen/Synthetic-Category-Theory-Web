# Uncurrying the cospan of compatible identifications

The left corner records a comparison of the underlying functors. The
middle corner records its triangle, and the right corner records the
comparison of maps to the terminal category. Uncurrying and changing
endpoints give equivalences on all three corners. The squares below are
identifications of functors on the entire comparison animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Param

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ComparisonCospan
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funUncurry-isoMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingCompatibility 𝒯 M ℱ
  using (funPost-uncurry-inputs)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
  using (changeEndpoints-map; changeEndpoints-map-isEquiv)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯
  using (change-map-evaluate)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeComparisonEncoding 𝒯 using (module Encoding)
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding as Relative
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (EvaluatedCone)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (evalMatch)
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameNaturality as ConstantName
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonAlgebra 𝒯
open Param vocabulary terminal products productLaws composition vertical using (const-cong)

module Uncurrying {X C D S : CAT} {f : MAP C S} {g : MAP D S}
  (s t : Cone (funPost g) (nameFun f) X) where
  module Source = Encoding s t
  module Target = Relative.Encoding 𝒯 M ℱ P (EvaluatedCone s) (EvaluatedCone t)
  fs = funPost-uncurry g (Cone.left s)
  ft = funPost-uncurry g (Cone.left t)
  κs = uncurry-constant-name f (Cone.right s)
  κt = uncurry-constant-name f (Cone.right t)
  τs = funUncurryIso (Cone.match s)
  τt = funUncurryIso (Cone.match t)

  left : MAP Source.Left Target.Left
  left = uncurryFamily (id Source.Left)
  right : MAP Source.Right One
  right = terminate Source.Right
  base : MAP Source.Middle Target.Middle
  base = changeEndpoints-map fs κt ∘ funUncurry-isoMap _ _

  opaque
    left-isEquiv : IsEquiv left
    left-isEquiv = equiv-transport
      (uncurryFamily-at (id Source.Left) ∙ (comp-unitʳ (funUncurry-isoMap _ _)) ⁻¹)
      (funUncurry-isoMap-isEquiv _ _)
    right-isEquiv : IsEquiv right
    right-isEquiv = terminalIso-isEquiv (Cone.right s) (Cone.right t)
    base-isEquiv : IsEquiv base
    base-isEquiv = equiv-compose (funUncurry-isoMap _ _) (changeEndpoints-map fs κt)
      (funUncurry-isoMap-isEquiv _ _) (changeEndpoints-map-isEquiv fs κt)

    base-at : {A : CAT} (δ : MAP A Source.Middle) →
      (base ∘ δ) =₁ (const κt ∙ (uncurryFamily δ ∙ const (fs ⁻¹)))
    base-at δ = isoComp-cong (idIso (const κt))
        (isoComp-cong (uncurryFamily-at δ) (idIso (const (fs ⁻¹)))) ∙
      (change-map-evaluate fs κt (funUncurry-isoMap _ _ ∘ δ) ∙
        comp-assoc δ (funUncurry-isoMap _ _) (changeEndpoints-map fs κt))

    uncurry-constant : {A : CAT} {a b : MAP X (Fun C S)} (α : a =₁ b) →
      uncurryFamily (const {P = A} α) =₁ const (funUncurryIso α)
    uncurry-constant α = const-cong ((funUncurryIso-at α) ⁻¹) ∙ uncurryFamily-constant α

    left-normalization : (Target.leftMap ∘ left) =₁ (const (evalMatch t) ∙ (g ◁ left))
    left-normalization = isoComp-cong (const-pre (evalMatch t) left) (idIso (g ◁ left)) ∙
      isoComp-pre (const (evalMatch t)) (postWhisker g) left

    post-family : (const ft ∙ uncurryFamily (postWhisker (funPost g))) =₁
      ((g ◁ left) ∙ const fs)
    post-family = funPost-uncurry-inputs g (id Source.Left) ∙
      isoComp-cong (idIso (const ft))
        (uncurryFamily-cong ((comp-unitʳ (postWhisker (funPost g))) ⁻¹))

    leftSquare : (Target.leftMap ∘ left) =₁ (base ∘ Source.leftMap)
    leftSquare = (base-at Source.leftMap) ⁻¹ ∙
      ((isoComp-cong (idIso (const κt))
        (isoComp-cong
          (isoComp-cong (uncurry-constant (Cone.match t)) (idIso _) ∙
            uncurryFamily-composition (const (Cone.match t)) (postWhisker (funPost g)))
          (idIso (const (fs ⁻¹))))) ⁻¹ ∙
      ((left-boundary fs ft τt κt (uncurryFamily (postWhisker (funPost g)))
          (g ◁ left) post-family) ⁻¹ ∙ left-normalization))

    rightSquare : (Target.rightMap ∘ right) =₁ (base ∘ Source.rightMap)
    rightSquare = (base-at Source.rightMap) ⁻¹ ∙
      ((isoComp-cong (idIso (const κt))
        (isoComp-cong
          (isoComp-cong (idIso _) (uncurry-constant (Cone.match s)) ∙
            uncurryFamily-composition (postWhisker (nameFun f)) (const (Cone.match s)))
          (idIso (const (fs ⁻¹))))) ⁻¹ ∙
      ((right-boundary fs τs κt κs (uncurryFamily (postWhisker (nameFun f)))
        (ConstantName.Family.natural 𝒯 M ℱ P f (id Source.Right) ∙
          isoComp-cong (idIso (const κt))
            (uncurryFamily-cong ((comp-unitʳ (postWhisker (nameFun f))) ⁻¹)))) ⁻¹ ∙
        const-pre (evalMatch s) right))

  cospan : CospanMap Source.leftMap Source.rightMap Target.leftMap Target.rightMap
  cospan = record { left = left ; right = right ; base = base
    ; leftSquare = leftSquare ; rightSquare = rightSquare }
```
