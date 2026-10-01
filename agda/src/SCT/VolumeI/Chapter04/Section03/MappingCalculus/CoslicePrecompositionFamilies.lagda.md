# Precomposition on arbitrary coslice families

The fixed hom family commutes with restriction. Consequently the usual
coslice precomposition functor acts on every family by composition with
that same fixed family. Its complete endpoint comparison is retained.

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

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CoslicePrecompositionFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (restrict-composition; retarget-composition)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (ConeIso; conePre; coneIso-compose)
import SCT.VolumeI.Chapter04.Section03.CoslicePrecomposition as Precomposition
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Reading
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as Lifting
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction as Restriction
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open Laws.PullbackStructure P using (pullbackCone)

module ForArrow {C : CAT} {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  private
    module Original = Precomposition.Along 𝒯 M ℱ P I E S {C = C} {x = x} {y = y} e
      using (functor; incoming; composite)
    module Arrow = At {C = C} {x = x} {y = y} e using (family; family-restrict)
    module Read = Reading.At 𝒯 M ℱ P I y using (read)
    module Lift = Lifting.At 𝒯 M ℱ P I x using (module Restrict; module Congruent)
    q = coslice-projection y
  open Original public using (functor)

  module AtFamily {Γ : CAT} (h : MAP Γ (Coslice C y)) where
    composite : MorphismExpression (const {P = Γ} x) (q ∘ h)
    composite = compose-expression (Arrow.family Γ) (Read.read h)
    private
      f = Arrow.family (Coslice C y)
      g = Original.incoming
      normalized = Restriction.restrict 𝒯 M ℱ I Original.composite h
      abstract
        expression-comparison : ExpressionIso normalized composite
        expression-comparison = expressionIso-compose
          (compose-expression-cong (Arrow.family-restrict h) (expressionIso-id (Read.read h)))
          (expressionIso-compose (expressionIso-inverse
            (retarget-composition (restrict-expression f h) (restrict-expression g h)
              (const-pre x h) (const-pre y h) (idIso (q ∘ h))))
            (retarget-expressionIso (expressionIso-inverse (restrict-composition f g h))
              (const-pre x h) (idIso (q ∘ h))))
      module Restricted = Lift.Restrict q Original.composite h using (specified-comparison; source-projection; base-computation)
      module Normal = Lift.Congruent {Γ = Γ} {b = q ∘ h}
        {f = normalized} {g = composite} expression-comparison using (specified-comparison; target-projection; base-computation)

    specified-comparison : ConeIso
      (conePre (functor ∘ h) (pullbackCone endpoints (pair (const x) (id C))))
      (conePre (coslice-intro x (q ∘ h) composite) (pullbackCone endpoints (pair (const x) (id C))))
    specified-comparison = coneIso-compose Normal.specified-comparison Restricted.specified-comparison
    source-projection = Restricted.source-projection
    target-projection = Normal.target-projection
    abstract
      base-computation : (target-projection ∙ ConeIso.rightIso specified-comparison) =₂ source-projection
      base-computation = Restricted.base-computation ∙
        isoComp-cong Normal.base-computation (idIso (ConeIso.rightIso Restricted.specified-comparison)) ∙
        (isoComp-assoc-at target-projection (ConeIso.rightIso Normal.specified-comparison)
          (ConeIso.rightIso Restricted.specified-comparison)) ⁻¹

    private
      module Reflected = Reflection.Lift 𝒯 P
        {f = endpoints} {g = pair (const {P = C} x) (id C)}
        (functor ∘ h) (coslice-intro x (q ∘ h) composite) specified-comparison
        using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)
```
