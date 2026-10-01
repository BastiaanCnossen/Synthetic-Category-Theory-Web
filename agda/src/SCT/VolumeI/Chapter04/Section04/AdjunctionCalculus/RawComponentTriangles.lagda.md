# Comparing raw triangles with their components

The four frame comparisons do not assume triangle equations. They apply
to a specified unit and counit while constructing an adjunction.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.RawComponentTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget-outer; retarget-cong; retarget-assoc; retarget-id; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso; restrict-expression-compose; restrict-expression-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I
  using (restrict-post)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (restrict-composition; retarget-composition)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdRestriction
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as TriangleUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as LeftUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered; pre-inverse-at)
open TriangleUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)
open LeftUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-post-retarget; restrict-restriction-retarget)

private
  corner : {Γ C D : CAT} (x : MAP Γ C) (l : MAP C D) (r : MAP D C) →
    (((l ∘ r) ∘ l) ∘ x) =₁ (l ∘ (r ∘ (l ∘ x)))
  corner x l r = comp-assoc (l ∘ x) r l ∙ comp-assoc x l (l ∘ r)

  corner-cancel : {Γ C D : CAT} (x : MAP Γ C) (l : MAP C D) (r : MAP D C) →
    (corner x l r ∙ ((comp-assoc l r l) ⁻¹ ▷ x)) =₂
    ((l ◁ comp-assoc x l r) ∙ comp-assoc x (r ∘ l) l)
  corner-cancel x l r = cancel-right (comp-assoc l r l ▷ x)
    ((l ◁ comp-assoc x l r) ∙ comp-assoc x (r ∘ l) l) ∙
    isoComp-cong
      ((isoComp-assoc-at (l ◁ comp-assoc x l r) (comp-assoc x (r ∘ l) l)
        (comp-assoc l r l ▷ x)) ⁻¹ ∙ pentagon-whiskered x l r l)
      (idIso ((comp-assoc l r l ▷ x) ⁻¹)) ∙
    isoComp-cong (idIso (corner x l r)) (pre-inverse-at (comp-assoc l r l) x)

  outer-id : {Γ Δ C : CAT} {f : MAP Γ C} (x : MAP Δ Γ)
    {z : MAP Δ C} (a : (f ∘ x) =₁ z) → (a ∙ (idIso f ▷ x)) =₂ a
  outer-id {f = f} x a = isoComp-unitʳ-at a ∙
    isoComp-cong (idIso a) (preWhisker-idIso f x)

import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UnitCounitData as Data
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdRetarget

module Components {C D : CAT} (l : MAP C D) (r : MAP D C)
  (unit : MorphismExpression (id C) (r ∘ l))
  (counit : MorphismExpression (l ∘ r) (id D)) where
  private module A = Data.Data 𝒯 M ℱ P I E S l r unit counit

  abstract
    left-unit-component : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (retarget-expression (restrict-expression A.left-unit x)
        (idIso (l ∘ x)) (corner x l r)) (post-expression l (A.unit-at x))
    left-unit-component x = expressionIso-compose (expressionIso-inverse (post-retarget l
      (restrict-expression unit x) (comp-unitˡ x) (comp-assoc x l r)))
      (restrict-post-retarget l unit x (comp-unitʳ l) ((comp-assoc l r l) ⁻¹)
        (idIso (l ∘ x)) (corner x l r) (l ◁ comp-unitˡ x) (l ◁ comp-assoc x l r)
        (triangle-whiskered x l ∙ isoComp-unitˡ-at (comp-unitʳ l ▷ x))
        (corner-cancel x l r))

    left-counit-component : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (retarget-expression (restrict-expression A.left-counit x)
        (corner x l r) (idIso (l ∘ x))) (A.counit-at (l ∘ x))
    left-counit-component x = restrict-restriction-retarget counit l x
      (idIso ((l ∘ r) ∘ l)) (comp-unitˡ l) (corner x l r) (idIso (l ∘ x))
      (comp-assoc (l ∘ x) r l) (comp-unitˡ (l ∘ x))
      (outer-id x (corner x l r))
      ((left-unitor-comp x l) ⁻¹ ∙ isoComp-unitˡ-at (comp-unitˡ l ▷ x))

    right-unit-component : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (retarget-expression (restrict-expression A.right-unit y)
        (idIso (r ∘ y)) (corner y r l)) (A.unit-at (r ∘ y))
    right-unit-component y = restrict-restriction-retarget unit r y
      (comp-unitˡ r) (idIso ((r ∘ l) ∘ r)) (idIso (r ∘ y)) (corner y r l)
      (comp-unitˡ (r ∘ y)) (comp-assoc (r ∘ y) l r)
      ((left-unitor-comp y r) ⁻¹ ∙ isoComp-unitˡ-at (comp-unitˡ r ▷ y))
      (outer-id y (corner y r l))

    right-counit-component : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (retarget-expression (restrict-expression A.right-counit y)
        (corner y r l) (idIso (r ∘ y))) (post-expression r (A.counit-at y))
    right-counit-component y = expressionIso-compose (expressionIso-inverse (post-retarget r
      (restrict-expression counit y) (comp-assoc y r l) (comp-unitˡ y)))
      (restrict-post-retarget r counit y ((comp-assoc r l r) ⁻¹) (comp-unitʳ r)
        (corner y r l) (idIso (r ∘ y)) (r ◁ comp-assoc y r l) (r ◁ comp-unitˡ y)
        (corner-cancel y r l)
        (triangle-whiskered y r ∙ isoComp-unitˡ-at (comp-unitʳ r ▷ y)))

    left-expanded : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (restrict-expression (compose-expression A.left-unit A.left-counit) x)
        (compose-expression (post-expression l (A.unit-at x)) (A.counit-at (l ∘ x)))
    left-expanded x = expressionIso-compose
      (compose-expression-cong (left-unit-component x) (left-counit-component x))
      (expressionIso-compose
        (expressionIso-inverse (retarget-composition (restrict-expression A.left-unit x)
          (restrict-expression A.left-counit x) (idIso (l ∘ x)) (corner x l r) (idIso (l ∘ x))))
        (expressionIso-compose (expressionIso-inverse (retarget-id _))
          (expressionIso-inverse (restrict-composition A.left-unit A.left-counit x))))

    right-expanded : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (restrict-expression (compose-expression A.right-unit A.right-counit) y)
        (compose-expression (A.unit-at (r ∘ y)) (post-expression r (A.counit-at y)))
    right-expanded y = expressionIso-compose
      (compose-expression-cong (right-unit-component y) (right-counit-component y))
      (expressionIso-compose
        (expressionIso-inverse (retarget-composition (restrict-expression A.right-unit y)
          (restrict-expression A.right-counit y) (idIso (r ∘ y)) (corner y r l) (idIso (r ∘ y))))
        (expressionIso-compose (expressionIso-inverse (retarget-id _))
          (expressionIso-inverse (restrict-composition A.right-unit A.right-counit y))))

  module FromComponents
    (left : ExpressionIso
      (compose-expression (post-expression l (A.unit-at (id C))) (A.counit-at (l ∘ id C)))
      (identity-expression (l ∘ id C)))
    (right : ExpressionIso
      (compose-expression (A.unit-at (r ∘ id D)) (post-expression r (A.counit-at (id D))))
      (identity-expression (r ∘ id D))) where

    abstract
      adjunction : Adjunction l r
      adjunction = record
        { unit = unit ; counit = counit
        ; left-triangle = expressionIso-compose (IdRetarget.At.comparison 𝒯 M ℱ P I E (comp-unitʳ l))
            (expressionIso-compose
              (retarget-expressionIso (expressionIso-compose left (left-expanded (id C))) (comp-unitʳ l) (comp-unitʳ l))
              (expressionIso-inverse (restrict-expression-id (compose-expression A.left-unit A.left-counit))))
        ; right-triangle = expressionIso-compose (IdRetarget.At.comparison 𝒯 M ℱ P I E (comp-unitʳ r))
            (expressionIso-compose
              (retarget-expressionIso (expressionIso-compose right (right-expanded (id D))) (comp-unitʳ r) (comp-unitʳ r))
              (expressionIso-inverse (restrict-expression-id (compose-expression A.right-unit A.right-counit)))) }

      unit-comparison : ExpressionIso (Adjunction.unit adjunction) unit
      unit-comparison = expressionIso-id unit

      counit-comparison : ExpressionIso (Adjunction.counit adjunction) counit
      counit-comparison = expressionIso-id counit
```
