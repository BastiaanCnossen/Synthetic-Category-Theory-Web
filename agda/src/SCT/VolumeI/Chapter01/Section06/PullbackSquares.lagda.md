# Pullback squares

As in `def:Pullback_Square`, a cone is a pullback square when its chosen
factorization into the pullback is an equivalence. The matching isomorphism
is part of the cone, so the property refers to that particular square.

The reusable calculations with cones are grouped in `ConeCalculus/`;
coordinate arguments are in `Coordinates/`. The universal property and
its uses below remain the main entry point.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.PullbackSquares
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)

IsPullback : {C D E T : CAT} {f : MAP C E} {g : MAP D E} → Cone f g T → Set m
IsPullback s = IsEquiv (pullbackLift s)

pullback-η : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h : MAP T (Pullback f g)) → (pullbackLift (conePre h (pullbackCone f g))) =₁ h
pullback-η {f = f} {g} h = pullback-reflect _ h (pullbackLift-β (conePre h (pullbackCone f g)))

pullbackCone-isPullback : {C D E : CAT} (f : MAP C E) (g : MAP D E) → IsPullback (pullbackCone f g)
pullbackCone-isPullback f g = equiv-transport
  ((pullback-reflect _ _ (coneIso-compose (coneIso-inverse (conePre-id (pullbackCone f g)))
    (pullbackLift-β (pullbackCone f g)))) ⁻¹) (id-isEquiv (Pullback f g))

pullbackLift-cong : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} → ConeIso s t → (pullbackLift s) =₁ (pullbackLift t)
pullbackLift-cong {s = s} {t} Φ = pullback-reflect _ _
  (coneIso-compose (coneIso-inverse (pullbackLift-β t)) (coneIso-compose Φ (pullbackLift-β s)))

pullback-cone-invariant : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} → ConeIso s t → IsPullback s → IsPullback t
pullback-cone-invariant Φ = equiv-transport (pullbackLift-cong Φ)

pullbackLift-restrict : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP S T) (s : Cone f g T) →
  (pullbackLift (conePre r s)) =₁ (pullbackLift s ∘ r)
pullbackLift-restrict {f = f} {g} r s = pullback-reflect _ _
  (coneIso-compose (conePre-assoc r (pullbackLift s) (pullbackCone f g))
    (coneIso-compose (coneIso-inverse (coneIso-pre r (pullbackLift-β s)))
      (pullbackLift-β (conePre r s))))

pullback-comparison : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g S) (t : Cone f g T) (h : MAP S T) →
  ConeIso (conePre h t) s → IsPullback s → IsPullback t → IsEquiv h
pullback-comparison s t h Φ es et = equiv-cancel-left h (pullbackLift t) et
  (equiv-transport (pullbackLift-restrict h t ∙ (pullbackLift-cong Φ) ⁻¹) es)

pullback-restrict-equivalence : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) (h : MAP S T) → IsPullback s → IsEquiv h →
  IsPullback (conePre h s)
pullback-restrict-equivalence s h es eh = equiv-transport ((pullbackLift-restrict h s) ⁻¹)
  (equiv-compose h (pullbackLift s) eh es)

module UniversalCone {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (t : Cone f g T) (et : IsPullback t) where

  factor : {S : CAT} → Cone f g S → MAP S T
  factor s = FunctorLift.lift (equiv-lift et (pullbackLift s))

  abstract
    factor-β : {S : CAT} (s : Cone f g S) → ConeIso (conePre (factor s) t) s
    factor-β s = coneIso-compose (pullbackLift-β s)
      (coneIso-compose (cone-action (pullbackCone f g)
        (FunctorLift.comparison (equiv-lift et (pullbackLift s))))
        (coneIso-compose (conePre-assoc (factor s) (pullbackLift t) (pullbackCone f g))
          (coneIso-inverse (coneIso-pre (factor s) (pullbackLift-β t)))))

    -- Retain the two projection computations without unfolding factor-β
    -- outside this abstract block.
    factor-β-left : {S : CAT} (s : Cone f g S) →
      (ConeIso.leftIso (factor-β s)) =₂
      (ConeIso.leftIso (pullbackLift-β s) ∙
        ((pullback₁ ◁ FunctorLift.comparison (equiv-lift et (pullbackLift s))) ∙
          (comp-assoc (factor s) (pullbackLift t) pullback₁ ∙
            (ConeIso.leftIso (pullbackLift-β t) ▷ factor s) ⁻¹)))
    factor-β-left s = idIso _

    factor-β-right : {S : CAT} (s : Cone f g S) →
      (ConeIso.rightIso (factor-β s)) =₂
      (ConeIso.rightIso (pullbackLift-β s) ∙
        ((pullback₂ ◁ FunctorLift.comparison (equiv-lift et (pullbackLift s))) ∙
          (comp-assoc (factor s) (pullbackLift t) pullback₂ ∙
            (ConeIso.rightIso (pullbackLift-β t) ▷ factor s) ⁻¹)))
    factor-β-right s = idIso _

  reflect : {S : CAT} (h k : MAP S T) →
    ConeIso (conePre h t) (conePre k t) → h =₁ k
  reflect h k Φ = equiv-reflect et h k
    (pullbackLift-restrict k t ∙ (pullbackLift-cong Φ ∙ (pullbackLift-restrict h t) ⁻¹))

  factor-η : {S : CAT} (h : MAP S T) → (factor (conePre h t)) =₁ h
  factor-η h = reflect _ h (factor-β (conePre h t))
```
