# Categories of arrows with specified endpoints

The pullback of the endpoint functor along a pair of functors retains the
arrow, its base parameter, and both endpoint identifications. This common
construction gives the hom and slice categories of Section 1.9.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.EndpointFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open Laws.PullbackStructure P

endpoints : {C : CAT} → MAP (Ar C) (C × C)
endpoints = pair ev₀ ev₁

module EndpointFiber {B C : CAT} (u v : MAP B C) where
  category : CAT
  category = Pullback endpoints (pair u v)

  arrow : MAP category (Ar C)
  arrow = pb₁

  base : MAP category B
  base = pb₂

  source-frame : =₁ (ev₀ ∘ arrow) (u ∘ base)
  source-frame = project-pair₁ u v base ∙
    ((pr₁ ◁ pbMatch) ∙ invIso (project-pair₁ ev₀ ev₁ arrow))

  target-frame : =₁ (ev₁ ∘ arrow) (v ∘ base)
  target-frame = project-pair₂ u v base ∙
    ((pr₂ ◁ pbMatch) ∙ invIso (project-pair₂ ev₀ ev₁ arrow))

  frame : MorphismExpression (u ∘ base) (v ∘ base)
  frame = record { arrow = arrow ; source-frame = source-frame ; target-frame = target-frame }

  cone : {Γ : CAT} (y : MAP Γ B) → MorphismExpression (u ∘ y) (v ∘ y) →
    Cone endpoints (pair u v) Γ
  cone y α = record
    { left = MorphismExpression.arrow α ; right = y
    ; match = invIso (pair-pre u v y) ∙
        (pair-cong (MorphismExpression.source-frame α) (MorphismExpression.target-frame α) ∙
          pair-pre ev₀ ev₁ (MorphismExpression.arrow α)) }

  lift : {Γ : CAT} (y : MAP Γ B) → MorphismExpression (u ∘ y) (v ∘ y) → MAP Γ category
  lift y α = pbLift (cone y α)

  lift-β : {Γ : CAT} (y : MAP Γ B) (α : MorphismExpression (u ∘ y) (v ∘ y)) →
    ConeIso (conePre (lift y α) (pbCone endpoints (pair u v))) (cone y α)
  lift-β y α = pbLift-β (cone y α)

  lift-arrow : {Γ : CAT} (y : MAP Γ B) (α : MorphismExpression (u ∘ y) (v ∘ y)) →
    =₁ (arrow ∘ lift y α) (MorphismExpression.arrow α)
  lift-arrow y α = pbLift-β₁ (cone y α)

  lift-base : {Γ : CAT} (y : MAP Γ B) (α : MorphismExpression (u ∘ y) (v ∘ y)) →
    =₁ (base ∘ lift y α) y
  lift-base y α = pbLift-β₂ (cone y α)
```
