# Universal arrows with their endpoint compatibility

Lift the prescribed base comparison through the equivalence of the slice
projection. The pullback comparison then supplies both endpoint equations.
This retains the data needed at the common vertex of a composite.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.UniversalComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.UniversalArrows 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section09.ExpressionComparisons 𝒯 M ℱ P I using (module Decode; reflect-retarget-comparison)
open import SCT.VolumeI.Chapter01.Section05.ConeCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Laws.PullbackStructure P

module Controlled {Γ B C : CAT} (u v : MAP B C)
  (universal : IsEquiv (EndpointFiber.base u v)) (y : MAP Γ B)
  (α β : MorphismExpression (u ∘ y) (v ∘ y)) where
  module F = EndpointFiber u v
  source-base = F.lift-base y α
  target-base = F.lift-base y β
  lift = postWhisker-lift F.base universal (invIso target-base ∙ source-base)
  γ = FunctorLift.lift lift

  cones : ConeIso (F.cone y α) (F.cone y β)
  cones = coneIso-compose (F.lift-β y β)
    (coneIso-compose (cone-action (pbCone endpoints (pair u v)) γ)
      (coneIso-inverse (F.lift-β y α)))

  base-identity : =₂ (ConeIso.rightIso cones) (idIso y)
  base-identity = isoComp-inverseʳ-at target-base ∙
    (isoComp-cong (idIso target-base) (cancel-right source-base (invIso target-base)) ∙
      isoComp-cong (idIso target-base) (isoComp-cong (FunctorLift.comparison lift) (idIso (invIso source-base))))

  comparison : ExpressionIso α β
  comparison = Decode.comparison u v y α β cones base-identity

initial-comparison : {Γ C : CAT} (x : Obj-abs C) → IsInitial x → (y : MAP Γ C) →
  (α β : MorphismExpression (const x) y) → ExpressionIso α β
initial-comparison {C = C} x e y α β = reflect-retarget-comparison α β
  (invIso (const-pre x y)) (invIso (comp-unitˡ y))
  (Controlled.comparison (const x) (id C) e y
    (retarget-expression α (invIso (const-pre x y)) (invIso (comp-unitˡ y)))
    (retarget-expression β (invIso (const-pre x y)) (invIso (comp-unitˡ y))))

terminal-comparison : {Γ C : CAT} (x : Obj-abs C) → IsTerminal x → (y : MAP Γ C) →
  (α β : MorphismExpression y (const x)) → ExpressionIso α β
terminal-comparison {C = C} x e y α β = reflect-retarget-comparison α β
  (invIso (comp-unitˡ y)) (invIso (const-pre x y))
  (Controlled.comparison (id C) (const x) e y
    (retarget-expression α (invIso (comp-unitˡ y)) (invIso (const-pre x y)))
    (retarget-expression β (invIso (comp-unitˡ y)) (invIso (const-pre x y))))
```


