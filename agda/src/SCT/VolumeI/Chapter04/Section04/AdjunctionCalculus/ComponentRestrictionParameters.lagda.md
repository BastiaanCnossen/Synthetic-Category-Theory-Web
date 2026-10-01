# Restricting and identifying adjunction parameters

A restricted unit or counit component can be evaluated at an identified
parameter. Both nested functor images remain in the endpoint frames.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestrictionParameters
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction as Restriction

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) where
  module A = Adjunction adj
  module Original = Restriction.Components 𝒯 M ℱ P I E S adj

  module Unit {Γ Δ : CAT} (x : MAP Γ C) (h : MAP Δ Γ) {y : MAP Δ C} (ξ : (x ∘ h) =₁ y) where
    θ = (r ◁ comp-assoc h x l) ∙ comp-assoc h (l ∘ x) r
    target-change = (r ◁ (l ◁ ξ)) ∙ θ
    abstract
      value : ExpressionIso (retarget-expression (restrict-expression (A.unit-at x) h) ξ target-change) (A.unit-at y)
      value = expressionIso-compose (Original.unit-parameter ξ)
        (expressionIso-compose (retarget-expressionIso (Original.unit-restrict x h) ξ (r ◁ (l ◁ ξ)))
          (expressionIso-compose (expressionIso-inverse (retarget-assoc (restrict-expression (A.unit-at x) h)
              (idIso (x ∘ h)) θ ξ (r ◁ (l ◁ ξ))))
            (retarget-cong (restrict-expression (A.unit-at x) h) ((isoComp-unitʳ-at ξ) ⁻¹) (idIso target-change))))

  module Counit {Γ Δ : CAT} (x : MAP Γ D) (h : MAP Δ Γ) {y : MAP Δ D} (ξ : (x ∘ h) =₁ y) where
    θ = (l ◁ comp-assoc h x r) ∙ comp-assoc h (r ∘ x) l
    source-change = (l ◁ (r ◁ ξ)) ∙ θ
    abstract
      value : ExpressionIso (retarget-expression (restrict-expression (A.counit-at x) h) source-change ξ) (A.counit-at y)
      value = expressionIso-compose (Original.counit-parameter ξ)
        (expressionIso-compose (retarget-expressionIso (Original.counit-restrict x h) (l ◁ (r ◁ ξ)) ξ)
          (expressionIso-compose (expressionIso-inverse (retarget-assoc (restrict-expression (A.counit-at x) h)
              θ (idIso (x ∘ h)) (l ◁ (r ◁ ξ)) ξ))
            (retarget-cong (restrict-expression (A.counit-at x) h) (idIso source-change) ((isoComp-unitʳ-at ξ) ⁻¹))))
```
