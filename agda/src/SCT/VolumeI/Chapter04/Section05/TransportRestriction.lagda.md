# Restriction of cartesian and cocartesian transport

The chosen lift is a composite of the lifting functor with the functor
represented by the input cone. Consequently it commutes with restriction
of that cone, even though the category of lifts need not be an anima.
The statements below retain the literal restricted cone. Comparing it
with a separately reframed expression is an additional endpoint calculation.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section05.TransportRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Transport 𝒯 M ℱ P I E S R public
open import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionIdentifications 𝒯 M ℱ P I E S R
  using (left-section-identification; right-section-identification)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.SplitComparisonLifts as Split

module CovariantRestriction {A B : CAT} (f : MAP A B) (w : Fibration.CocartesianFibration f)
  {Γ : CAT} (x : MAP Γ A) (y : MAP Γ B)
  (β : MorphismExpression (f ∘ x) y) where
  private
    module T = Covariant f w x y β
    module D = Evaluation f
    module W = Fibration.CocartesianFibration w
    module L = Split.Split 𝒯 P (D.Left.cone ev₀ (f ∘ ev₁) D.left-expression)
      W.lift (left-section-identification W.left-adjoint-section)

  module Restrict {Δ : CAT} (r : MAP Δ Γ) where
    restricted-lift = L.At.factor (conePre r T.target-cone)

    comparison : restricted-lift =₁ (T.lift ∘ r)
    comparison = L.At.restrict T.target-cone r

    transport-comparison : (ev₁ ∘ restricted-lift) =₁ (T.transport ∘ r)
    transport-comparison = (comp-assoc r T.lift ev₁) ⁻¹ ∙ (ev₁ ◁ comparison)

module ContravariantRestriction {A B : CAT} (f : MAP A B) (w : Fibration.CartesianFibration f)
  {Γ : CAT} (x : MAP Γ B) (y : MAP Γ A)
  (β : MorphismExpression x (f ∘ y)) where
  private
    module T = Contravariant f w x y β
    module D = Evaluation f
    module W = Fibration.CartesianFibration w
    module L = Split.Split 𝒯 P (D.Right.cone (f ∘ ev₀) ev₁ D.right-expression)
      W.lift (right-section-identification W.right-adjoint-section)

  module Restrict {Δ : CAT} (r : MAP Δ Γ) where
    restricted-lift = L.At.factor (conePre r T.target-cone)

    comparison : restricted-lift =₁ (T.lift ∘ r)
    comparison = L.At.restrict T.target-cone r

    transport-comparison : (ev₀ ∘ restricted-lift) =₁ (T.transport ∘ r)
    transport-comparison = (comp-assoc r T.lift ev₀) ⁻¹ ∙ (ev₀ ◁ comparison)
```
