# Uniqueness and restriction of chosen lifts

A prescribed lift includes its whole comparison with the directed
endpoint cone. Left or right fibrancy identifies it with the chosen
lift. The comparison has the prescribed image in the arrow category
of the base and the prescribed pair of endpoints.

The restriction statement uses the literal restricted endpoint cone.
It compares factoring that cone with restricting the chosen lift. Thus
it does not silently replace the cone's matching by an unrelated one.
Identifying this input with a separately reframed expression is a
distinct endpoint calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section02.TransportComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section02.Transport 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (module UniversalCone)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalFactorComparisons as Factors

module CovariantComparison {A B : CAT} (f : MAP A B) (e : Fibration.IsLeftFibration f)
  {Γ : CAT} (x : MAP Γ A) (y : MAP Γ B)
  (β : MorphismExpression (f ∘ x) y) where
  private module T = Covariant f e x y β
  private module D = Evaluation f
  universal = D.Left.cone ev₀ (f ∘ ev₁) D.left-expression
  private module U = UniversalCone universal e using (factor)

  module Compare (h : MAP Γ (Ar A)) (w : ConeIso (conePre h universal) T.target-cone) where
    private
      module K = Factors.At.Compare 𝒯 P universal e T.target-cone h w
        using (comparison; left-image; right-image)

    lift-comparison : T.lift =₁ h
    lift-comparison = K.comparison

    transport-comparison : T.transport =₁ (ev₁ ∘ h)
    transport-comparison = ev₁ ◁ lift-comparison

    image : (funPost f ◁ lift-comparison) =₂
      ((ConeIso.leftIso w) ⁻¹ ∙ ConeIso.leftIso T.lift-β)
    image = K.left-image

    endpoint-image : (pair ev₀ (f ∘ ev₁) ◁ lift-comparison) =₂
      ((ConeIso.rightIso w) ⁻¹ ∙ ConeIso.rightIso T.lift-β)
    endpoint-image = K.right-image

  module Restrict {Δ : CAT} (r : MAP Δ Γ) where
    restricted-lift : MAP Δ (Ar A)
    restricted-lift = U.factor (conePre r T.target-cone)

    comparison : restricted-lift =₁ (T.lift ∘ r)
    comparison = Factors.At.Restrict.comparison 𝒯 P universal e T.target-cone r

    transport-comparison : (ev₁ ∘ restricted-lift) =₁ (T.transport ∘ r)
    transport-comparison = (comp-assoc r T.lift ev₁) ⁻¹ ∙ (ev₁ ◁ comparison)

module ContravariantComparison {A B : CAT} (f : MAP A B) (e : Fibration.IsRightFibration f)
  {Γ : CAT} (x : MAP Γ B) (y : MAP Γ A)
  (β : MorphismExpression x (f ∘ y)) where
  private module T = Contravariant f e x y β
  private module D = Evaluation f
  universal = D.Right.cone (f ∘ ev₀) ev₁ D.right-expression
  private module U = UniversalCone universal e using (factor)

  module Compare (h : MAP Γ (Ar A)) (w : ConeIso (conePre h universal) T.target-cone) where
    private
      module K = Factors.At.Compare 𝒯 P universal e T.target-cone h w
        using (comparison; left-image; right-image)

    lift-comparison : T.lift =₁ h
    lift-comparison = K.comparison

    transport-comparison : T.transport =₁ (ev₀ ∘ h)
    transport-comparison = ev₀ ◁ lift-comparison

    image : (funPost f ◁ lift-comparison) =₂
      ((ConeIso.leftIso w) ⁻¹ ∙ ConeIso.leftIso T.lift-β)
    image = K.left-image

    endpoint-image : (pair (f ∘ ev₀) ev₁ ◁ lift-comparison) =₂
      ((ConeIso.rightIso w) ⁻¹ ∙ ConeIso.rightIso T.lift-β)
    endpoint-image = K.right-image

  module Restrict {Δ : CAT} (r : MAP Δ Γ) where
    restricted-lift : MAP Δ (Ar A)
    restricted-lift = U.factor (conePre r T.target-cone)

    comparison : restricted-lift =₁ (T.lift ∘ r)
    comparison = Factors.At.Restrict.comparison 𝒯 P universal e T.target-cone r

    transport-comparison : (ev₀ ∘ restricted-lift) =₁ (T.transport ∘ r)
    transport-comparison = (comp-assoc r T.lift ev₀) ⁻¹ ∙ (ev₀ ◁ comparison)
```
