# Arrows from initial objects and into terminal objects

The equivalence defining a universal object supplies families of arrows
and compares any two such families with the same endpoints. The proof
uses the actual slice lifts and their projection comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.UniversalArrows
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public

module UniversalEndpoints {B C : CAT} (u v : MAP B C)
  (universal : IsEquiv (EndpointFiber.base u v)) where
  module Fiber = EndpointFiber u v

  chosen : {Γ : CAT} (y : MAP Γ B) → MorphismExpression (u ∘ y) (v ∘ y)
  chosen y = retarget-expression (restrict-expression Fiber.frame h)
    ((u ◁ β) ∙ comp-assoc h Fiber.base u)
    ((v ◁ β) ∙ comp-assoc h Fiber.base v)
    where
    h = FunctorLift.lift (equiv-lift universal y)
    β = FunctorLift.comparison (equiv-lift universal y)

  compare : {Γ : CAT} (y : MAP Γ B)
    (α β : MorphismExpression (u ∘ y) (v ∘ y)) →
    (MorphismExpression.arrow α) =₁ (MorphismExpression.arrow β)
  compare y α β = Fiber.lift-arrow y β ∙
    ((Fiber.arrow ◁ FunctorLift.lift (postWhisker-lift Fiber.base universal
      ((Fiber.lift-base y β) ⁻¹ ∙ Fiber.lift-base y α))) ∙ (Fiber.lift-arrow y α) ⁻¹)

initial-expression : {Γ C : CAT} (x : Obj-abs C) → IsInitial x → (y : MAP Γ C) →
  MorphismExpression (const x) y
initial-expression {C = C} x e y = retarget-expression
  (UniversalEndpoints.chosen (const x) (id C) e y) (const-pre x y) (comp-unitˡ y)

terminal-expression : {Γ C : CAT} (x : Obj-abs C) → IsTerminal x → (y : MAP Γ C) →
  MorphismExpression y (const x)
terminal-expression {C = C} x e y = retarget-expression
  (UniversalEndpoints.chosen (id C) (const x) e y) (comp-unitˡ y) (const-pre x y)

initial-compare : {Γ C : CAT} (x : Obj-abs C) → IsInitial x → (y : MAP Γ C) →
  (α β : MorphismExpression (const x) y) →
  (MorphismExpression.arrow α) =₁ (MorphismExpression.arrow β)
initial-compare {C = C} x e y α β = UniversalEndpoints.compare (const x) (id C) e y
  (retarget-expression α ((const-pre x y) ⁻¹) ((comp-unitˡ y) ⁻¹))
  (retarget-expression β ((const-pre x y) ⁻¹) ((comp-unitˡ y) ⁻¹))

terminal-compare : {Γ C : CAT} (x : Obj-abs C) → IsTerminal x → (y : MAP Γ C) →
  (α β : MorphismExpression y (const x)) →
  (MorphismExpression.arrow α) =₁ (MorphismExpression.arrow β)
terminal-compare {C = C} x e y α β = UniversalEndpoints.compare (id C) (const x) e y
  (retarget-expression α ((comp-unitˡ y) ⁻¹) ((const-pre x y) ⁻¹))
  (retarget-expression β ((comp-unitˡ y) ⁻¹) ((const-pre x y) ⁻¹))
```

