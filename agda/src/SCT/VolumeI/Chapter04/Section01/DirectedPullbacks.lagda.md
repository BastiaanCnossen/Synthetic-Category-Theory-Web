# Directed pullbacks

For `cons:Directed_Pullback`, take the pullback of the endpoint functor
along the product of the two given functors. The construction is absolute;
the parameter of a cone may be any absolute category. The full-subcategory
description of ordinary pullbacks is a separate, deferred assertion.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.DirectedPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointFibers 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open Laws.PullbackStructure P public

module DirectedPullback {A B C : CAT} (f : MAP A C) (g : MAP B C) where
  category : CAT
  category = Pullback endpoints (productMap f g)

  diagram : MAP category (Ar C)
  diagram = pullback₁

  base : MAP category (A × B)
  base = pullback₂

  left : MAP category A
  left = pr₁ ∘ base

  right : MAP category B
  right = pr₂ ∘ base

  matching : (endpoints ∘ diagram) =₁ (productMap f g ∘ base)
  matching = pullbackMatch

  source-frame : (ev₀ ∘ diagram) =₁ (f ∘ left)
  source-frame = comp-assoc base pr₁ f ∙
    (project-pair₁ (f ∘ pr₁) (g ∘ pr₂) base ∙
      ((pr₁ ◁ matching) ∙ (project-pair₁ ev₀ ev₁ diagram) ⁻¹))

  target-frame : (ev₁ ∘ diagram) =₁ (g ∘ right)
  target-frame = comp-assoc base pr₂ g ∙
    (project-pair₂ (f ∘ pr₁) (g ∘ pr₂) base ∙
      ((pr₂ ◁ matching) ∙ (project-pair₂ ev₀ ev₁ diagram) ⁻¹))

  universal-expression : MorphismExpression (f ∘ left) (g ∘ right)
  universal-expression = record
    { arrow = diagram ; source-frame = source-frame ; target-frame = target-frame }

  cone : {Γ : CAT} (x : MAP Γ A) (y : MAP Γ B) →
    MorphismExpression (f ∘ x) (g ∘ y) → Cone endpoints (productMap f g) Γ
  cone x y α = record
    { left = MorphismExpression.arrow α ; right = pair x y
    ; match = (productMap-pair f g x y) ⁻¹ ∙
        (pair-cong (MorphismExpression.source-frame α) (MorphismExpression.target-frame α) ∙
          pair-pre ev₀ ev₁ (MorphismExpression.arrow α)) }

  intro : {Γ : CAT} (x : MAP Γ A) (y : MAP Γ B) →
    MorphismExpression (f ∘ x) (g ∘ y) → MAP Γ category
  intro x y α = pullbackLift (cone x y α)

  intro-β : {Γ : CAT} (x : MAP Γ A) (y : MAP Γ B)
    (α : MorphismExpression (f ∘ x) (g ∘ y)) →
    ConeIso (conePre (intro x y α) (pullbackCone endpoints (productMap f g))) (cone x y α)
  intro-β x y α = pullbackLift-β (cone x y α)
```

`intro-β` retains both leg comparisons and their compatibility with the
specified matching identification. It is stronger than a comparison of
the underlying categories or an unframed identification of diagrams.
