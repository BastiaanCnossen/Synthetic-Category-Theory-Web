# Universal arrows with their endpoint compatibility

Lift the prescribed base comparison through the equivalence of the slice
projection. The pullback comparison then supplies both endpoint equations.
This retains the data needed at the common vertex of a composite.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.DiagramCalculus.UniversalComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.UniversalArrows 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.ExpressionComparisons 𝒯 M ℱ P I using (module Decode; reflect-retarget-comparison)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Laws.PullbackStructure P

module Controlled {Γ B C : CAT} (u v : MAP B C)
  (universal : IsEquiv (EndpointFiber.base u v)) (y : MAP Γ B)
  (α β : MorphismExpression (u ∘ y) (v ∘ y)) where
  module F = EndpointFiber u v
  source-base = F.lift-base y α
  target-base = F.lift-base y β
  lift = postWhisker-lift F.base universal (target-base ⁻¹ ∙ source-base)
  γ = FunctorLift.lift lift

  cones : ConeIso (F.cone y α) (F.cone y β)
  cones = coneIso-compose (F.lift-β y β)
    (coneIso-compose (cone-action (pullbackCone endpoints (pair u v)) γ)
      (coneIso-inverse (F.lift-β y α)))

  base-identity : (ConeIso.rightIso cones) =₂ (idIso y)
  base-identity = isoComp-inverseʳ-at target-base ∙
    (isoComp-cong (idIso target-base) (cancel-right source-base (target-base ⁻¹)) ∙
      isoComp-cong (idIso target-base) (isoComp-cong (FunctorLift.comparison lift) (idIso (source-base ⁻¹))))

  comparison : ExpressionIso α β
  comparison = Decode.comparison u v y α β cones base-identity

initial-comparison : {Γ C : CAT} (x : Obj-abs C) → IsInitial x → (y : MAP Γ C) →
  (α β : MorphismExpression (const x) y) → ExpressionIso α β
initial-comparison {C = C} x e y α β = reflect-retarget-comparison α β
  ((const-pre x y) ⁻¹) ((comp-unitˡ y) ⁻¹)
  (Controlled.comparison (const x) (id C) e y
    (retarget-expression α ((const-pre x y) ⁻¹) ((comp-unitˡ y) ⁻¹))
    (retarget-expression β ((const-pre x y) ⁻¹) ((comp-unitˡ y) ⁻¹)))

terminal-comparison : {Γ C : CAT} (x : Obj-abs C) → IsTerminal x → (y : MAP Γ C) →
  (α β : MorphismExpression y (const x)) → ExpressionIso α β
terminal-comparison {C = C} x e y α β = reflect-retarget-comparison α β
  ((comp-unitˡ y) ⁻¹) ((const-pre x y) ⁻¹)
  (Controlled.comparison (id C) (const x) e y
    (retarget-expression α ((comp-unitˡ y) ⁻¹) ((const-pre x y) ⁻¹))
    (retarget-expression β ((comp-unitˡ y) ⁻¹) ((const-pre x y) ⁻¹)))
```


