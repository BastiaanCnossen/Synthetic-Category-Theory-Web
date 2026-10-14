# Pullback cones in equivalent cospans

Pass through the chosen pullbacks to replace a cospan by an equivalent
one. The two projection computations restore the requested leg maps.
The matching is the transported matching of this whole cone, and is
therefore part of the construction, rather than an arbitrary
identification between its composites.
The factor comparison below also computes the whole cone before its
legs are retargeted, retaining the specified cospan matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as Cospans

module SCT.VolumeI.Chapter01.Section06.Cospans.EquivalentCospanCone
  {c m a : Level} (𝒯 : Theory c m a) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)

module Transport {A B C A′ B′ C′ X : CAT}
  {u : MAP A C} {v : MAP B C} {u′ : MAP A′ C′} {v′ : MAP B′ C′}
  (F : CospanMap u v u′ v′)
  (ei : IsEquiv (CospanMap.left F)) (ej : IsEquiv (CospanMap.right F)) (ek : IsEquiv (CospanMap.base F))
  (s : Cone u v X) (universal : IsPullback s) where
  module Changed = CospanMap F
  module Equivalence = CospanEquivalence F ei ej ek using (pullbackMap-isEquiv)
  module Action = Cospans.Action 𝒯 P F using (map-iso; map-pre)
  abstract
    factor : MAP X (Pullback u′ v′)
    factor = Changed.pullbackMap ∘ pullbackLift s
    factor-isEquiv : IsEquiv factor
    factor-isEquiv = equiv-compose (pullbackLift s) Changed.pullbackMap universal Equivalence.pullbackMap-isEquiv
    factor-cone : ConeIso (conePre factor (pullbackCone u′ v′)) (Changed.mapCone s)
    factor-cone = coneIso-compose (Action.map-iso (pullbackLift-β s))
      (coneIso-compose
        (coneIso-inverse (Action.map-pre (pullbackLift s) (pullbackCone u v)))
        (coneIso-compose (coneIso-pre (pullbackLift s) Changed.pullbackMap-β)
          (coneIso-inverse (conePre-assoc (pullbackLift s) Changed.pullbackMap (pullbackCone u′ v′)))))
    left-comparison : (pullback₁ ∘ factor) =₁ (Changed.left ∘ Cone.left s)
    left-comparison = (Changed.left ◁ pullbackLift-β₁ s) ∙
      (comp-assoc (pullbackLift s) pullback₁ Changed.left ∙
        ((ConeIso.leftIso Changed.pullbackMap-β ▷ pullbackLift s) ∙
          (comp-assoc (pullbackLift s) Changed.pullbackMap pullback₁) ⁻¹))
    right-comparison : (pullback₂ ∘ factor) =₁ (Changed.right ∘ Cone.right s)
    right-comparison = (Changed.right ◁ pullbackLift-β₂ s) ∙
      (comp-assoc (pullbackLift s) pullback₂ Changed.right ∙
        ((ConeIso.rightIso Changed.pullbackMap-β ▷ pullbackLift s) ∙
          (comp-assoc (pullbackLift s) Changed.pullbackMap pullback₂) ⁻¹))
  original = conePre factor (pullbackCone u′ v′)
  cone : Cone u′ v′ X
  cone = coneRetarget original (Changed.left ∘ Cone.left s) (Changed.right ∘ Cone.right s)
    left-comparison right-comparison
  abstract
    comparison : ConeIso original cone
    comparison = coneRetarget-β original (Changed.left ∘ Cone.left s) (Changed.right ∘ Cone.right s)
      left-comparison right-comparison
    isPullback : IsPullback cone
    isPullback = pullback-cone-invariant comparison
      (equiv-transport ((pullback-η factor) ⁻¹) factor-isEquiv)
```
