# Invertible families of morphisms

Two inverse equations for framed morphism expressions give a lift of
the whole family to `Iso C`. The construction uses the two Segal
triangles and their specified long-edge comparisons. This extends
`rmk:Lift_To_Iso_Iff_Invertible` to an arbitrary absolute parameter.

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

module SCT.VolumeI.Chapter02.Section03.InvertibleExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E
  using (Iso; IsoLift; InverseTriangles; inverseLongEdges; inverseIdentityEdges; isoArrow; isoTriangles)
open import SCT.VolumeI.Chapter02.Section03.UniversalInverseExpressions 𝒯 M ℱ P I E S
  using (IsInvertibleExpression)
import SCT.VolumeI.Chapter02.Section03.ConstantIdentityComparison as Constant
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open Laws.PullbackStructure P

module LiftInverse {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (g h : MorphismExpression y x)
  (right-law : ExpressionIso (compose-expression g f) (identity-expression y))
  (left-law : ExpressionIso (compose-expression f h) (identity-expression x)) where
  module Right = Complete (expression-pair g f)
  module Left = Complete (expression-pair f h)
  right-common = ConeIso.rightIso Right.short-edges
  left-common = ConeIso.leftIso Left.short-edges

  common : Cone (edge₀ {C}) edge₂ Γ
  common = record
    { left = Right.triangle ; right = Left.triangle
    ; match = left-common ⁻¹ ∙ right-common }

  triangles : MAP Γ (InverseTriangles C)
  triangles = pullbackLift common

  right-long : ((edge₁ ∘ pullback₁) ∘ triangles) =₁ (identityArrow ∘ y)
  right-long = (ExpressionIso.comparison (Constant.At.comparison 𝒯 M ℱ P I E y)) ⁻¹ ∙
    (ExpressionIso.comparison right-law ∙
      ((edge₁ ◁ pullbackLift-β₁ common) ∙ comp-assoc triangles pullback₁ edge₁))

  left-long : ((edge₁ ∘ pullback₂) ∘ triangles) =₁ (identityArrow ∘ x)
  left-long = (ExpressionIso.comparison (Constant.At.comparison 𝒯 M ℱ P I E x)) ⁻¹ ∙
    (ExpressionIso.comparison left-law ∙
      ((edge₁ ◁ pullbackLift-β₂ common) ∙ comp-assoc triangles pullback₂ edge₁))

  identities-at-objects : (inverseIdentityEdges C ∘ pair x y) =₁
    (pair (identityArrow ∘ y) (identityArrow ∘ x))
  identities-at-objects = pair-cong
    ((identityArrow ◁ pair-β₂ x y) ∙ comp-assoc (pair x y) pr₂ identityArrow)
    ((identityArrow ◁ pair-β₁ x y) ∙ comp-assoc (pair x y) pr₁ identityArrow) ∙
    pair-pre (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) (pair x y)

  inverse-cone : Cone (inverseLongEdges C) (inverseIdentityEdges C) Γ
  inverse-cone = record
    { left = triangles ; right = pair x y
    ; match = identities-at-objects ⁻¹ ∙
        (pair-cong right-long left-long ∙
          pair-pre (edge₁ ∘ pullback₁) (edge₁ ∘ pullback₂) triangles) }

  value : MAP Γ (Iso C)
  value = pullbackLift inverse-cone

  arrow-comparison : (isoArrow ∘ value) =₁ (MorphismExpression.arrow f)
  arrow-comparison = right-common ∙
    ((edge₀ ◁ pullbackLift-β₁ common) ∙
      (comp-assoc triangles pullback₁ edge₀ ∙
        (((edge₀ ∘ pullback₁) ◁ pullbackLift-β₁ inverse-cone) ∙
          comp-assoc value isoTriangles (edge₀ ∘ pullback₁))))

  lift : IsoLift (MorphismExpression.arrow f)
  lift = record { lift = value ; comparison = arrow-comparison }

invertible-expression-lift : {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) → IsInvertibleExpression f → IsoLift (MorphismExpression.arrow f)
invertible-expression-lift f w = LiftInverse.lift f
  (IsInvertibleExpression.right-inverse w) (IsInvertibleExpression.left-inverse w)
  (IsInvertibleExpression.right-inverse-law w) (IsInvertibleExpression.left-inverse-law w)
```
