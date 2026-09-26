# Lifting a family at three specified points

If an anima is presented by three points, a family on that anima lifts
through a functor once its restrictions at the three points lift. We
first glue the three restrictions using coproducts, then reflect along
the specified equivalence. No pointwise choice principle is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts

module SCT.VolumeI.Chapter03.Section01.MappingCalculus.FiniteMappingLifts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B
  using (copair; copair-β₁; copair-β₂)
open import SCT.VolumeI.Chapter03.Section01.Lifting.CoproductLifting 𝒯 M B
  using (mapPre-mapPost; lift-coproduct)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
  using (coreInclusion; core-of-anima; module CoreLift)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M using (coreInclusion-natural)

retarget-lift : {Γ X Y : CAT} {m : MAP X Y} {h k : MAP Γ Y} →
  h =₁ k → FunctorLift m h → FunctorLift m k
retarget-lift α l = record { lift = FunctorLift.lift l ; comparison = α ∙ FunctorLift.comparison l }

restriction-compose : {Γ A B C D : CAT} (f : MAP A B) (g : MAP B C) (h : MAP Γ (Map C D)) →
  (mapPre f ∘ (mapPre g ∘ h)) =₁ (mapPre (g ∘ f) ∘ h)
restriction-compose f g h = (mapPre-comp f g ▷ h) ∙ (comp-assoc h (mapPre g) (mapPre f)) ⁻¹

module AlongEquivalence {Γ K L X Y : CAT} (e : MAP K L) (ee : IsEquiv e)
  (m : MAP X Y) (h : MAP Γ (Map L Y))
  (restricted : FunctorLift (mapPost m) (mapPre e ∘ h)) where
  chosen = equiv-lift (mapPre-isEquiv e ee) (FunctorLift.lift restricted)
  lift = FunctorLift.lift chosen

  comparison : (mapPost m ∘ lift) =₁ h
  comparison = equiv-reflect (mapPre-isEquiv e ee) _ _
    (FunctorLift.comparison restricted ∙
      ((mapPost m ◁ FunctorLift.comparison chosen) ∙
        (comp-assoc lift (mapPre e) (mapPost m) ∙
          ((mapPre-mapPost e m ▷ lift) ∙ (comp-assoc lift (mapPost m) (mapPre e)) ⁻¹))))

  factorization : FunctorLift (mapPost m) h
  factorization = record { lift = lift ; comparison = comparison }

module ThreePoints {K : CAT} (x₀ x₁ x₂ : Obj-abs K)
  (points-isEquiv : IsEquiv (copair (copair x₀ x₁) x₂)) where

  points = copair (copair x₀ x₁) x₂

  module Lift {Γ X Y : CAT} (m : MAP X Y) (h : MAP Γ (Map K Y))
    (at₀ : FunctorLift (mapPost m) (mapPre x₀ ∘ h))
    (at₁ : FunctorLift (mapPost m) (mapPre x₁ ∘ h))
    (at₂ : FunctorLift (mapPost m) (mapPre x₂ ∘ h)) where

    whole = mapPre points ∘ h
    firstTwo = mapPre in₁ ∘ whole

    firstTwo-comparison : firstTwo =₁ (mapPre (copair x₀ x₁) ∘ h)
    firstTwo-comparison = (mapPre-cong (copair-β₁ (copair x₀ x₁) x₂) ▷ h) ∙
      restriction-compose in₁ points h

    first-comparison : (mapPre in₁ ∘ firstTwo) =₁ (mapPre x₀ ∘ h)
    first-comparison = (mapPre-cong (copair-β₁ x₀ x₁) ▷ h) ∙
      (restriction-compose in₁ (copair x₀ x₁) h ∙ (mapPre in₁ ◁ firstTwo-comparison))

    second-comparison : (mapPre in₂ ∘ firstTwo) =₁ (mapPre x₁ ∘ h)
    second-comparison = (mapPre-cong (copair-β₂ x₀ x₁) ▷ h) ∙
      (restriction-compose in₂ (copair x₀ x₁) h ∙ (mapPre in₂ ◁ firstTwo-comparison))

    third-comparison : (mapPre in₂ ∘ whole) =₁ (mapPre x₂ ∘ h)
    third-comparison = (mapPre-cong (copair-β₂ (copair x₀ x₁) x₂) ▷ h) ∙
      restriction-compose in₂ points h

    restricted : FunctorLift (mapPost m) whole
    restricted = lift-coproduct m whole
      (lift-coproduct m firstTwo (retarget-lift (first-comparison ⁻¹) at₀)
        (retarget-lift (second-comparison ⁻¹) at₁))
      (retarget-lift (third-comparison ⁻¹) at₂)

    factorization : FunctorLift (mapPost m) h
    factorization = AlongEquivalence.factorization points points-isEquiv m h restricted

  lift-three : {Γ X Y : CAT} (m : MAP X Y) (h : MAP Γ (Map K Y)) →
    FunctorLift (mapPost m) (mapPre x₀ ∘ h) →
    FunctorLift (mapPost m) (mapPre x₁ ∘ h) →
    FunctorLift (mapPost m) (mapPre x₂ ∘ h) → FunctorLift (mapPost m) h
  lift-three = Lift.factorization
```

At an individual point, lifting after the inclusion of the core suffices.
The source is an anima, so the lift itself has a canonical core lift.

```agda
lift-core-family : {Γ X Y : CAT} (Γ-an : isAn Γ) (Y-an : isAn Y)
  (m : MAP X Y) (h : MAP Γ (Map One Y)) →
  FunctorLift m (coreInclusion Y ∘ h) → FunctorLift (mapPost m) h
lift-core-family {Γ} {X} {Y} Γ-an Y-an m h l = record
  { lift = L.lift
  ; comparison = equiv-reflect (core-of-anima Y Y-an) _ _
      (FunctorLift.comparison l ∙
        ((m ◁ L.comparison) ∙
          (comp-assoc L.lift (coreInclusion X) m ∙
            ((coreInclusion-natural m ▷ L.lift) ∙
              (comp-assoc L.lift (mapPost m) (coreInclusion Y)) ⁻¹)))) }
  where module L = CoreLift Γ-an (FunctorLift.lift l) using (lift; comparison)
```
