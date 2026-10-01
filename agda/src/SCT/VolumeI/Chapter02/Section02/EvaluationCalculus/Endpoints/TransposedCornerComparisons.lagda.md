# Transporting a whole corner into a family of diagrams

A corner is a square together with its specified commutativity
identification. Transposing a comparison of its two edges preserves
that identification. This applies separately to the middle, source,
and target corners of a triangle, with an arbitrary absolute category
of parameters.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.TransposedCornerComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeTransposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunRestrictionCones 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunctorCriterionDetection as Evaluated
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.TransposedSquareEvaluation as Transposed
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunSquareEvaluation as FunEvaluation
import SCT.VolumeI.Chapter01.Section08.FunctorCategoryCalculus.FunPrecompositionComposition as FunComposition
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ

module Edge {Γ A T C : CAT} (k : MAP T (Fun Γ C)) (r : MAP A T)
  (f : MAP A (Fun Γ C)) (δ : (k ∘ r) =₁ f) where
  family = funCurry (transpose k)
  target = funCurry (transpose f)

  raw : (funUncurry (funPre r ∘ family)) =₁ (funUncurry target)
  raw = (funCurry-β (transpose f)) ⁻¹ ∙
    (transposeIso δ ∙ ((transpose-pre r k) ⁻¹ ∙
      ((funCurry-β (transpose k) ▷ productRestriction Γ r) ∙ funPre-uncurry r family)))

  comparison : (funPre r ∘ family) =₁ target
  comparison = funIsoReflect _ _ raw

  comparison-β : funUncurryIso comparison =₂ raw
  comparison-β = funIsoReflect-β _ _ raw

module Corner {Γ A B D T C : CAT}
  {u : MAP A B} {v : MAP A D} {p : MAP B T} {q : MAP D T}
  (s : Square u v p q) (k : MAP T (Fun Γ C))
  (boundary : Cocone u v (Fun Γ C))
  (edges : CoconeIso (coconePost k (squareCocone s)) boundary) where

  family : MAP Γ (Fun T C)
  family = funCurry (transpose k)

  transposed-boundary : Cocone (productRestriction Γ u) (productRestriction Γ v) C
  transposed-boundary = transposeCocone boundary

  module Boundary = CurryRestriction {u = u} {v = v} transposed-boundary

  module LeftEdge = Edge k p (Cocone.left boundary) (CoconeIso.leftIso edges)
    using (comparison; raw)
  module RightEdge = Edge k q (Cocone.right boundary) (CoconeIso.rightIso edges)
    using (comparison; raw)
  module EvaluatedFamily = FunEvaluation.Evaluation 𝒯 M ℱ P s family
    (FunComposition.CompositorEvaluation.comparison 𝒯 M ℱ P u p family)
    (FunComposition.CompositorEvaluation.comparison 𝒯 M ℱ P v q family)
    using (comparison-left; comparison-right)

  abstract
    uncurried-corner : CoconeIso
      (uncurryRestriction {u = u} {v = v} (conePre family (functorOut s C)))
      transposed-boundary
    uncurried-corner = coconeIso-compose (transposeCoconeIso edges)
      (coconeIso-compose
        (coconeIso-inverse (Transposed.Evaluation.comparison 𝒯 M ℱ s k))
        (coconeIso-compose (restriction-action s (funCurry-β (transpose k)))
          (Evaluated.Evaluated.fun-evaluate 𝒯 M ℱ P s C family)))

    raw-comparison : CoconeIso
      (uncurryRestriction {u = u} {v = v} (conePre family (functorOut s C)))
      (uncurryRestriction {u = u} {v = v} Boundary.value)
    raw-comparison = coconeIso-compose (coconeIso-inverse Boundary.comparison) uncurried-corner

    raw-left : CoconeIso.leftIso raw-comparison =₂ LeftEdge.raw
    raw-left = isoComp-cong (＝-inv ◁ Boundary.comparison-left)
      (isoComp-cong (idIso (transposeIso (CoconeIso.leftIso edges)))
        (isoComp-cong (＝-inv ◁ Transposed.Evaluation.comparison-left 𝒯 M ℱ s k)
          (isoComp-cong (idIso (funCurry-β (transpose k) ▷ productRestriction Γ p))
            EvaluatedFamily.comparison-left)))

    raw-right : CoconeIso.rightIso raw-comparison =₂ RightEdge.raw
    raw-right = isoComp-cong (＝-inv ◁ Boundary.comparison-right)
      (isoComp-cong (idIso (transposeIso (CoconeIso.rightIso edges)))
        (isoComp-cong (＝-inv ◁ Transposed.Evaluation.comparison-right 𝒯 M ℱ s k)
          (isoComp-cong (idIso (funCurry-β (transpose k) ▷ productRestriction Γ q))
            EvaluatedFamily.comparison-right)))

  specified-edges : CoconeIso
    (uncurryRestriction {u = u} {v = v} (conePre family (functorOut s C)))
    (uncurryRestriction {u = u} {v = v} Boundary.value)
  specified-edges = coconeIso-adjust raw-comparison LeftEdge.raw RightEdge.raw raw-left raw-right

  module Reflected = ReflectRestriction {u = u} {v = v}
    (conePre family (functorOut s C)) Boundary.value specified-edges
    using (comparison; comparison-left; comparison-right)

  abstract
    comparison : ConeIso (conePre family (functorOut s C)) Boundary.value
    comparison = Reflected.comparison

    comparison-left : ConeIso.leftIso comparison =₂ LeftEdge.comparison
    comparison-left = Reflected.comparison-left

    comparison-right : ConeIso.rightIso comparison =₂ RightEdge.comparison
    comparison-right = Reflected.comparison-right
```
