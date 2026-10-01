# Restriction of unit and counit components

The component at a composite parameter map agrees with the restricted
component. The endpoint changes display both nested functors. These
comparisons provide the restriction equations needed to assemble the
transposition formulas into functors between total categories.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-restriction-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expression-parameter)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as LeftUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open LeftUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-id-at; postWhisker-comp-at)

module Components {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) where
  private module A = Adjunction adj

  abstract
    unit-restrict : {Γ Δ : CAT} (x : MAP Γ C) (h : MAP Δ Γ) →
      ExpressionIso (retarget-expression (restrict-expression (A.unit-at x) h)
        (idIso (x ∘ h))
        ((r ◁ comp-assoc h x l) ∙ comp-assoc h (l ∘ x) r))
        (A.unit-at (x ∘ h))
    unit-restrict x h = restrict-restriction-retarget A.unit x h
      (comp-unitˡ x) (comp-assoc x l r) (idIso (x ∘ h))
      ((r ◁ comp-assoc h x l) ∙ comp-assoc h (l ∘ x) r)
      (comp-unitˡ (x ∘ h)) (comp-assoc (x ∘ h) l r)
      ((left-unitor-comp h x) ⁻¹ ∙ isoComp-unitˡ-at (comp-unitˡ x ▷ h))
      ((pentagon-whiskered h x l r) ⁻¹ ∙
        isoComp-assoc-at (r ◁ comp-assoc h x l) (comp-assoc h (l ∘ x) r) (comp-assoc x l r ▷ h))

    counit-restrict : {Γ Δ : CAT} (y : MAP Γ D) (h : MAP Δ Γ) →
      ExpressionIso (retarget-expression (restrict-expression (A.counit-at y) h)
        ((l ◁ comp-assoc h y r) ∙ comp-assoc h (r ∘ y) l)
        (idIso (y ∘ h))) (A.counit-at (y ∘ h))
    counit-restrict y h = restrict-restriction-retarget A.counit y h
      (comp-assoc y r l) (comp-unitˡ y)
      ((l ◁ comp-assoc h y r) ∙ comp-assoc h (r ∘ y) l) (idIso (y ∘ h))
      (comp-assoc (y ∘ h) r l) (comp-unitˡ (y ∘ h))
      ((pentagon-whiskered h y r l) ⁻¹ ∙
        isoComp-assoc-at (l ◁ comp-assoc h y r) (comp-assoc h (r ∘ y) l) (comp-assoc y r l ▷ h))
      ((left-unitor-comp h y) ⁻¹ ∙ isoComp-unitˡ-at (comp-unitˡ y ▷ h))

    unit-parameter : {Γ : CAT} {x x′ : MAP Γ C} (ξ : x =₁ x′) →
      ExpressionIso (retarget-expression (A.unit-at x) ξ (r ◁ (l ◁ ξ))) (A.unit-at x′)
    unit-parameter {x = x} {x′} ξ = expressionIso-compose
      (retarget-expressionIso (restrict-expression-parameter A.unit ξ)
        (comp-unitˡ x′) (comp-assoc x′ l r))
      (expressionIso-compose (expressionIso-inverse
        (retarget-assoc (restrict-expression A.unit x) (id C ◁ ξ) ((r ∘ l) ◁ ξ)
          (comp-unitˡ x′) (comp-assoc x′ l r)))
        (expressionIso-compose
          (retarget-cong (restrict-expression A.unit x)
            ((postWhisker-id-at ξ) ⁻¹) ((postWhisker-comp-at ξ l r) ⁻¹))
          (retarget-assoc (restrict-expression A.unit x) (comp-unitˡ x) (comp-assoc x l r)
            ξ (r ◁ (l ◁ ξ)))))

    counit-parameter : {Γ : CAT} {y y′ : MAP Γ D} (ξ : y =₁ y′) →
      ExpressionIso (retarget-expression (A.counit-at y) (l ◁ (r ◁ ξ)) ξ) (A.counit-at y′)
    counit-parameter {y = y} {y′} ξ = expressionIso-compose
      (retarget-expressionIso (restrict-expression-parameter A.counit ξ)
        (comp-assoc y′ r l) (comp-unitˡ y′))
      (expressionIso-compose (expressionIso-inverse
        (retarget-assoc (restrict-expression A.counit y) ((l ∘ r) ◁ ξ) (id D ◁ ξ)
          (comp-assoc y′ r l) (comp-unitˡ y′)))
        (expressionIso-compose
          (retarget-cong (restrict-expression A.counit y)
            ((postWhisker-comp-at ξ r l) ⁻¹) ((postWhisker-id-at ξ) ⁻¹))
          (retarget-assoc (restrict-expression A.counit y) (comp-assoc y r l) (comp-unitˡ y)
            (l ◁ (r ◁ ξ)) ξ)))
```
