# Precomposition by an object of a coslice

An object of `C_{x/}` determines a fixed arrow with target `y`.
Composition with its constant family defines a functor from `C_{y/}`
to `C_{x/}`. Its action on every family is retained as a normalized
expression, for use with the iterated-coslice projection.

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

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceObjectPrecomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (restrict-composition; retarget-composition)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction as Restriction
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Expressions
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceLifts as Lifts
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceObjectArrows as Arrows
import SCT.VolumeI.Chapter04.Section03.CoslicePrecomposition as Standard
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose)

module At {C : CAT} (x : Obj-abs C) (u : Obj-abs (Coslice C x)) where
  y : Obj-abs C
  y = coslice-projection x ∘ u

  private
    module ReadX = Expressions.At 𝒯 M ℱ P I x using (universal; read)
    module ReadY = Expressions.At 𝒯 M ℱ P I y using (universal; read)
    module Fixed = Restriction.Fixed 𝒯 M ℱ I ReadX.universal u using (family; module Restrict)
    module Lift = Lifts.At 𝒯 M ℱ P I x using (congruence; module Restrict; module Congruent)
    q = coslice-projection y
  open Fixed public using (family)

  composite : MorphismExpression (const x) q
  composite = compose-expression (family (Coslice C y)) ReadY.universal

  functor : MAP (Coslice C y) (Coslice C x)
  functor = coslice-intro x q composite

  module Restricted {Γ : CAT} (h : MAP Γ (Coslice C y)) where
    private
      f = family (Coslice C y)
      g = ReadY.universal
      normalized = Restriction.restrict 𝒯 M ℱ I composite h
      f′ = retarget-expression (restrict-expression f h) (const-pre x h) (const-pre y h)
      g′ = ReadY.read h
    abstract
      expression-computation : ExpressionIso normalized (compose-expression (family Γ) g′)
      expression-computation = expressionIso-compose
        (compose-expression-cong (Fixed.Restrict.comparison h) (expressionIso-id g′))
        (expressionIso-compose (expressionIso-inverse
          (retarget-composition (restrict-expression f h) (restrict-expression g h)
            (const-pre x h) (const-pre y h) (idIso (q ∘ h))))
          (retarget-expressionIso (expressionIso-inverse (restrict-composition f g h))
            (const-pre x h) (idIso (q ∘ h))))

    private
      module RestrictedLift = Lift.Restrict q composite h using (specified-comparison)
      module ChangedLift = Lift.Congruent {Γ = Γ} {b = q ∘ h}
        {f = normalized} {g = compose-expression (family Γ) g′} expression-computation using (specified-comparison)
    specified-comparison = coneIso-compose ChangedLift.specified-comparison RestrictedLift.specified-comparison
    private
      module Reflected = Reflection.Lift 𝒯 P (functor ∘ h)
        (coslice-intro x (q ∘ h) (compose-expression (family Γ) (ReadY.read h)))
        specified-comparison using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)

  private
    module Represented = Arrows.At 𝒯 M ℱ P I x u using (point; module Family)
    module HomPre = Standard.Along 𝒯 M ℱ P I E S {C = C} {x = x} {y = y} Represented.point
      using (functor; composite)
    abstract
      hom-expression-comparison : ExpressionIso composite HomPre.composite
      hom-expression-comparison = compose-expression-cong
        (expressionIso-inverse (Represented.Family.comparison (Coslice C y)))
        (expressionIso-id ReadY.universal)
    module HomComparison = Lift.Congruent {Γ = Coslice C y} {b = q}
      {f = composite} {g = HomPre.composite} hom-expression-comparison
      using (comparison; comparison-image; left-image; right-image; specified-comparison)

  hom-point = Represented.point
  standard-precompose = HomPre.functor
  open HomComparison public renaming
    (comparison to standard-comparison; comparison-image to standard-image;
     left-image to standard-arrow; right-image to standard-target;
     specified-comparison to standard-computation)
```
