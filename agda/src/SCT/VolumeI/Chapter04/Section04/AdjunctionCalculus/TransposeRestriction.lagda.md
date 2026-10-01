# Transposition commutes with restriction

The transposition formulas commute with a change of parameter category.
The associators in the statement retain the specified endpoints, so the
comparison applies to the universal expressions in endpoint pullbacks.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-cong; retarget-assoc)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-post-frames)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (restrict-composition; retarget-composition)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons as Comparisons

module RestrictionLaws {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) where
  private
    module A = Adjunction adj
    module N = Comparisons.Comparisons 𝒯 M ℱ P I E S adj
      using (transpose-cong; untranspose-cong; transpose-retarget; untranspose-retarget)
    module R = Restriction.Components 𝒯 M ℱ P I E S adj using (unit-restrict; counit-restrict)

  abstract
    transpose-restrict : {Γ Δ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      (α : MorphismExpression (l ∘ x) y) (h : MAP Δ Γ) →
      ExpressionIso
        (retarget-expression (restrict-expression (A.transpose x y α) h)
          (idIso (x ∘ h)) (comp-assoc h y r))
        (A.transpose (x ∘ h) (y ∘ h)
          (retarget-expression (restrict-expression α h)
            (comp-assoc h x l) (idIso (y ∘ h))))
    transpose-restrict x y α h = expressionIso-compose
      (compose-expression-cong (R.unit-restrict x h)
        (expressionIso-compose
          (restrict-post-frames r α h (comp-assoc h x l) (idIso (y ∘ h)))
          (retarget-cong (restrict-expression (post-expression r α) h)
            (idIso _) ((isoComp-unitˡ-at (comp-assoc h y r) ∙
              isoComp-cong (postWhisker-idIso r (y ∘ h)) (idIso (comp-assoc h y r))) ⁻¹))))
      (expressionIso-compose
        (expressionIso-inverse (retarget-composition
          (restrict-expression (A.unit-at x) h) (restrict-expression (post-expression r α) h)
          (idIso (x ∘ h)) ((r ◁ comp-assoc h x l) ∙ comp-assoc h (l ∘ x) r)
          (comp-assoc h y r)))
        (retarget-expressionIso (expressionIso-inverse (restrict-composition (A.unit-at x) (post-expression r α) h))
          (idIso (x ∘ h)) (comp-assoc h y r)))

    untranspose-restrict : {Γ Δ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      (β : MorphismExpression x (r ∘ y)) (h : MAP Δ Γ) →
      ExpressionIso
        (retarget-expression (restrict-expression (A.untranspose x y β) h)
          (comp-assoc h x l) (idIso (y ∘ h)))
        (A.untranspose (x ∘ h) (y ∘ h)
          (retarget-expression (restrict-expression β h)
            (idIso (x ∘ h)) (comp-assoc h y r)))
    untranspose-restrict x y β h = expressionIso-compose
      (compose-expression-cong
        (expressionIso-compose
          (restrict-post-frames l β h (idIso (x ∘ h)) (comp-assoc h y r))
          (retarget-cong (restrict-expression (post-expression l β) h)
            ((isoComp-unitˡ-at (comp-assoc h x l) ∙
              isoComp-cong (postWhisker-idIso l (x ∘ h)) (idIso (comp-assoc h x l))) ⁻¹) (idIso _)))
        (R.counit-restrict y h))
      (expressionIso-compose
        (expressionIso-inverse (retarget-composition
          (restrict-expression (post-expression l β) h) (restrict-expression (A.counit-at y) h)
          (comp-assoc h x l) ((l ◁ comp-assoc h y r) ∙ comp-assoc h (r ∘ y) l)
          (idIso (y ∘ h))))
        (retarget-expressionIso (expressionIso-inverse (restrict-composition (post-expression l β) (A.counit-at y) h))
          (comp-assoc h x l) (idIso (y ∘ h))))

    transpose-restrict-change : {Γ Δ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      (α : MorphismExpression (l ∘ x) y) (h : MAP Δ Γ) {x′ : MAP Δ C} {y′ : MAP Δ D}
      (ξ : (x ∘ h) =₁ x′) (ζ : (y ∘ h) =₁ y′) →
      ExpressionIso (retarget-expression (restrict-expression (A.transpose x y α) h)
        ξ ((r ◁ ζ) ∙ comp-assoc h y r))
        (A.transpose x′ y′ (retarget-expression (restrict-expression α h)
          ((l ◁ ξ) ∙ comp-assoc h x l) ζ))
    transpose-restrict-change x y α h {x′} {y′} ξ ζ = expressionIso-compose
      (N.transpose-cong x′ y′ (expressionIso-compose
        (retarget-cong (restrict-expression α h) (idIso _) (isoComp-unitʳ-at ζ))
        (retarget-assoc (restrict-expression α h) (comp-assoc h x l) (idIso (y ∘ h)) (l ◁ ξ) ζ)))
      (expressionIso-compose
        (N.transpose-retarget (retarget-expression (restrict-expression α h) (comp-assoc h x l) (idIso (y ∘ h))) ξ ζ)
        (expressionIso-compose (retarget-expressionIso (transpose-restrict x y α h) ξ (r ◁ ζ))
          (expressionIso-compose
            (expressionIso-inverse (retarget-assoc (restrict-expression (A.transpose x y α) h)
              (idIso (x ∘ h)) (comp-assoc h y r) ξ (r ◁ ζ)))
            (retarget-cong (restrict-expression (A.transpose x y α) h) ((isoComp-unitʳ-at ξ) ⁻¹) (idIso _)))))

    untranspose-restrict-change : {Γ Δ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      (β : MorphismExpression x (r ∘ y)) (h : MAP Δ Γ) {x′ : MAP Δ C} {y′ : MAP Δ D}
      (ξ : (x ∘ h) =₁ x′) (ζ : (y ∘ h) =₁ y′) →
      ExpressionIso (retarget-expression (restrict-expression (A.untranspose x y β) h)
        ((l ◁ ξ) ∙ comp-assoc h x l) ζ)
        (A.untranspose x′ y′ (retarget-expression (restrict-expression β h)
          ξ ((r ◁ ζ) ∙ comp-assoc h y r)))
    untranspose-restrict-change x y β h {x′} {y′} ξ ζ = expressionIso-compose
      (N.untranspose-cong x′ y′ (expressionIso-compose
        (retarget-cong (restrict-expression β h) (isoComp-unitʳ-at ξ) (idIso _))
        (retarget-assoc (restrict-expression β h) (idIso (x ∘ h)) (comp-assoc h y r) ξ (r ◁ ζ))))
      (expressionIso-compose
        (N.untranspose-retarget (retarget-expression (restrict-expression β h) (idIso (x ∘ h)) (comp-assoc h y r)) ξ ζ)
        (expressionIso-compose (retarget-expressionIso (untranspose-restrict x y β h) (l ◁ ξ) ζ)
          (expressionIso-compose
            (expressionIso-inverse (retarget-assoc (restrict-expression (A.untranspose x y β) h)
              (comp-assoc h x l) (idIso (y ∘ h)) (l ◁ ξ) ζ))
            (retarget-cong (restrict-expression (A.untranspose x y β) h) (idIso _) ((isoComp-unitʳ-at ζ) ⁻¹)))))
```
