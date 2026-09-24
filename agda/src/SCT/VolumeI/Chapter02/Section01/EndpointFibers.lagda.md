# Categories of arrows with specified endpoints

The pullback of the endpoint functor along a pair of functors retains the
arrow, its base parameter, and both endpoint identifications. This common
construction gives the hom and slice categories of Section 2.1.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.EndpointFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open Laws.PullbackStructure P

endpoints : {C : CAT} → MAP (Ar C) (C × C)
endpoints = pair ev₀ ev₁

module EndpointFiber {B C : CAT} (u v : MAP B C) where
  category : CAT
  category = Pullback endpoints (pair u v)

  arrow : MAP category (Ar C)
  arrow = pullback₁

  base : MAP category B
  base = pullback₂

  source-frame : (ev₀ ∘ arrow) =₁ (u ∘ base)
  source-frame = project-pair₁ u v base ∙
    ((pr₁ ◁ pullbackMatch) ∙ (project-pair₁ ev₀ ev₁ arrow) ⁻¹)

  target-frame : (ev₁ ∘ arrow) =₁ (v ∘ base)
  target-frame = project-pair₂ u v base ∙
    ((pr₂ ◁ pullbackMatch) ∙ (project-pair₂ ev₀ ev₁ arrow) ⁻¹)

  frame : MorphismExpression (u ∘ base) (v ∘ base)
  frame = record { arrow = arrow ; source-frame = source-frame ; target-frame = target-frame }

  cone : {Γ : CAT} (y : MAP Γ B) → MorphismExpression (u ∘ y) (v ∘ y) →
    Cone endpoints (pair u v) Γ
  cone y α = record
    { left = MorphismExpression.arrow α ; right = y
    ; match = (pair-pre u v y) ⁻¹ ∙
        (pair-cong (MorphismExpression.source-frame α) (MorphismExpression.target-frame α) ∙
          pair-pre ev₀ ev₁ (MorphismExpression.arrow α)) }

  lift : {Γ : CAT} (y : MAP Γ B) → MorphismExpression (u ∘ y) (v ∘ y) → MAP Γ category
  lift y α = pullbackLift (cone y α)

  lift-β : {Γ : CAT} (y : MAP Γ B) (α : MorphismExpression (u ∘ y) (v ∘ y)) →
    ConeIso (conePre (lift y α) (pullbackCone endpoints (pair u v))) (cone y α)
  lift-β y α = pullbackLift-β (cone y α)

  lift-arrow : {Γ : CAT} (y : MAP Γ B) (α : MorphismExpression (u ∘ y) (v ∘ y)) →
    (arrow ∘ lift y α) =₁ (MorphismExpression.arrow α)
  lift-arrow y α = pullbackLift-β₁ (cone y α)

  lift-base : {Γ : CAT} (y : MAP Γ B) (α : MorphismExpression (u ∘ y) (v ∘ y)) →
    (base ∘ lift y α) =₁ y
  lift-base y α = pullbackLift-β₂ (cone y α)
```
