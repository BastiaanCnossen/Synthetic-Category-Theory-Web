# Relative functors out of a coproduct

Restriction to the two summands is an equivalence of relative functor
categories. Its inverse copairs the two universal families. The native
restriction computations prove the inverse laws, including the base
triangles; the argument applies over an arbitrary absolute base.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter03.RelativeCategories.CoproductCalculus.CoproductMapping
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section06.Distributivity 𝒯 M B P U using (module Distributivity)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Coproducts 𝒯 M ℱ P B using (module Sum)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.ArgumentFamilies 𝒯 M ℱ P using (module Argument)

open import SCT.VolumeI.Chapter03.RelativeCategories.CoproductCalculus.CoproductFamilies 𝒯 M ℱ P B U using (module Families)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)

module Restriction {C D E S : CAT} (p : MAP C S) (q : MAP D S) (r : MAP E S) where
  module Domain = Sum p q using (projection; first; second)
  module Left = Precompose r Domain.first using (functor; family-comparison)
  module Right = Precompose r Domain.second using (functor; family-comparison)
  module LeftArgument = Argument Domain.first using (family)
  module RightArgument = Argument Domain.second using (family)
  Source = FunOver Domain.projection r
  Target = FunOver p r × FunOver q r
  functor : MAP Source Target
  functor = pair Left.functor Right.functor
  module Chosen = Families.Copair p q r Target (family p r pr₁) (family q r pr₂)
    using (value; first-comparison; second-comparison)
  inverse : MAP Target Source
  inverse = Curry.functor Domain.projection r (FunctorLift.lift Chosen.value) (FunctorLift.comparison Chosen.value)

  abstract
    inverse-evaluation : FunctorOverIso (family Domain.projection r inverse) Chosen.value
    inverse-evaluation = curried-beta Domain.projection r Chosen.value

    first-comparison : (Left.functor ∘ inverse) =₁ pr₁
    first-comparison = reflect-family p r _ _
      (compose-iso-over Chosen.first-comparison
        (compose-iso-over (prewhisker-over (LeftArgument.family Target) inverse-evaluation)
          (Left.family-comparison inverse)))
    second-comparison : (Right.functor ∘ inverse) =₁ pr₂
    second-comparison = reflect-family q r _ _
      (compose-iso-over Chosen.second-comparison
        (compose-iso-over (prewhisker-over (RightArgument.family Target) inverse-evaluation)
          (Right.family-comparison inverse)))
    right-inverse : (functor ∘ inverse) =₁ id Target
    right-inverse = pair-projections ∙
      (pair-cong first-comparison second-comparison ∙ pair-pre Left.functor Right.functor inverse)

    reflect : {X : CAT} (F G : MAP X Source) → (functor ∘ F) =₁ (functor ∘ G) → F =₁ G
    reflect {X} F G α = reflect-family Domain.projection r F G
      (Families.Compare.comparison p q r X (family Domain.projection r F) (family Domain.projection r G)
        (compose-iso-over (Left.family-comparison G)
          (compose-iso-over (family-identification p r
            (project-pair₁ Left.functor Right.functor G ∙
              ((pr₁ ◁ α) ∙ (project-pair₁ Left.functor Right.functor F) ⁻¹)))
            (inverse-iso-over (Left.family-comparison F))))
        (compose-iso-over (Right.family-comparison G)
          (compose-iso-over (family-identification q r
            (project-pair₂ Left.functor Right.functor G ∙
              ((pr₂ ◁ α) ∙ (project-pair₂ Left.functor Right.functor F) ⁻¹)))
            (inverse-iso-over (Right.family-comparison F)))))

    left-inverse : (inverse ∘ functor) =₁ id Source
    left-inverse = reflect (inverse ∘ functor) (id Source)
      ((comp-unitʳ functor) ⁻¹ ∙
        (comp-unitˡ functor ∙ ((right-inverse ▷ functor) ∙ (comp-assoc functor inverse functor) ⁻¹)))

    functor-isEquiv : IsEquiv functor
    functor-isEquiv = record { inverse = inverse ; sectionIso = left-inverse ⁻¹ ; retractionIso = right-inverse ⁻¹ }
```
