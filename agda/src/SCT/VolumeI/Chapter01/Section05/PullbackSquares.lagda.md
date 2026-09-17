# Pullback squares

As in `def:Pullback_Square`, a cone is a pullback square when its chosen
factorization into the pullback is an equivalence. The matching isomorphism
is part of the cone, so the property refers to that particular square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.PullbackSquares
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.ConeRestriction 𝒯 public
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.ConeAction 𝒯 using (cone-action)

IsPullback : {C D E T : CAT} {f : MAP C E} {g : MAP D E} → Cone f g T → Set m
IsPullback s = IsEquiv (pbLift s)

pullback-η : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h : MAP T (Pullback f g)) → NatIso (pbLift (conePre h (pbCone f g))) h
pullback-η {f = f} {g} h = pullback-reflect _ h (pbLift-β (conePre h (pbCone f g)))

pbCone-isPullback : {C D E : CAT} (f : MAP C E) (g : MAP D E) → IsPullback (pbCone f g)
pbCone-isPullback f g = equiv-transport
  (invIso (pullback-reflect _ _ (coneIso-compose (coneIso-inverse (conePre-id (pbCone f g)))
    (pbLift-β (pbCone f g))))) (id-isEquiv (Pullback f g))

pbLift-cong : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} → ConeIso s t → NatIso (pbLift s) (pbLift t)
pbLift-cong {s = s} {t} Φ = pullback-reflect _ _
  (coneIso-compose (coneIso-inverse (pbLift-β t)) (coneIso-compose Φ (pbLift-β s)))

pullback-cone-invariant : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} → ConeIso s t → IsPullback s → IsPullback t
pullback-cone-invariant Φ = equiv-transport (pbLift-cong Φ)

pbLift-pre : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP S T) (s : Cone f g T) →
  NatIso (pbLift (conePre r s)) (pbLift s ∘ r)
pbLift-pre {f = f} {g} r s = pullback-reflect _ _
  (coneIso-compose (conePre-assoc r (pbLift s) (pbCone f g))
    (coneIso-compose (coneIso-inverse (coneIso-pre r (pbLift-β s)))
      (pbLift-β (conePre r s))))

pullback-comparison : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g S) (t : Cone f g T) (h : MAP S T) →
  ConeIso (conePre h t) s → IsPullback s → IsPullback t → IsEquiv h
pullback-comparison s t h Φ es et = equiv-cancel-left h (pbLift t) et
  (equiv-transport (pbLift-pre h t ∙ invIso (pbLift-cong Φ)) es)

pullback-restrict-equivalence : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) (h : MAP S T) → IsPullback s → IsEquiv h →
  IsPullback (conePre h s)
pullback-restrict-equivalence s h es eh = equiv-transport (invIso (pbLift-pre h s))
  (equiv-compose h (pbLift s) eh es)

module UniversalCone {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (t : Cone f g T) (et : IsPullback t) where

  factor : {S : CAT} → Cone f g S → MAP S T
  factor s = FunctorLift.lift (equiv-lift et (pbLift s))

  abstract
    factor-β : {S : CAT} (s : Cone f g S) → ConeIso (conePre (factor s) t) s
    factor-β s = coneIso-compose (pbLift-β s)
      (coneIso-compose (cone-action (pbCone f g)
        (FunctorLift.comparison (equiv-lift et (pbLift s))))
        (coneIso-compose (conePre-assoc (factor s) (pbLift t) (pbCone f g))
          (coneIso-inverse (coneIso-pre (factor s) (pbLift-β t)))))

  reflect : {S : CAT} (h k : MAP S T) →
    ConeIso (conePre h t) (conePre k t) → NatIso h k
  reflect h k Φ = equiv-reflect et h k
    (pbLift-pre k t ∙ (pbLift-cong Φ ∙ invIso (pbLift-pre h t)))

  factor-η : {S : CAT} (h : MAP S T) → NatIso (factor (conePre h t)) h
  factor-η h = reflect _ h (factor-β (conePre h t))
```
