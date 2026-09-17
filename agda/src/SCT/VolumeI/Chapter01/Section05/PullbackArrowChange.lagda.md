# Pullbacks and isomorphic cospan arrows

Replacing a cospan arrow by a specified naturally isomorphic functor
preserves pullback squares. The comparison uses that specified isomorphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.PullbackArrowChange
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.ConeArrowChange 𝒯
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P

module ChangeLeft {C D E : CAT} {f f′ : MAP C E} (α : =₁ f f′) (g : MAP D E) where

  source = pbCone f g
  target = pbCone f′ g
  forward = pbLift (changeLeft α source)
  backward = pbLift (changeLeft (invIso α) target)

  backward-forward : =₁ (backward ∘ forward) (id (Pullback f g))
  backward-forward = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id source))
    (coneIso-compose (changeLeft-back α source)
    (coneIso-compose (changeLeft-iso (invIso α) (pbLift-β (changeLeft α source)))
    (coneIso-compose (changeLeft-pre (invIso α) forward target)
    (coneIso-compose (coneIso-pre forward (pbLift-β (changeLeft (invIso α) target)))
      (coneIso-inverse (conePre-assoc forward backward source)))))))

  forward-backward : =₁ (forward ∘ backward) (id (Pullback f′ g))
  forward-backward = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id target))
    (coneIso-compose (changeLeft-backʳ α target)
    (coneIso-compose (changeLeft-iso α (pbLift-β (changeLeft (invIso α) target)))
    (coneIso-compose (changeLeft-pre α backward source)
    (coneIso-compose (coneIso-pre backward (pbLift-β (changeLeft α source)))
      (coneIso-inverse (conePre-assoc backward forward target)))))))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward ; sectionIso = invIso backward-forward ; retractionIso = invIso forward-backward }

  factorization : {T : CAT} (s : Cone f g T) →
    =₁ (pbLift (changeLeft α s)) (forward ∘ pbLift s)
  factorization s = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse image) (pbLift-β (changeLeft α s)))
    where
    image = coneIso-compose (changeLeft-iso α (pbLift-β s))
      (coneIso-compose (changeLeft-pre α (pbLift s) source)
      (coneIso-compose (coneIso-pre (pbLift s) (pbLift-β (changeLeft α source)))
        (coneIso-inverse (conePre-assoc (pbLift s) forward target))))

  preserve : {T : CAT} (s : Cone f g T) → IsPullback s → IsPullback (changeLeft α s)
  preserve s es = equiv-transport (invIso (factorization s))
    (equiv-compose (pbLift s) forward es forward-isEquiv)

  reflect : {T : CAT} (s : Cone f g T) → IsPullback (changeLeft α s) → IsPullback s
  reflect s es = equiv-cancel-left (pbLift s) forward forward-isEquiv
    (equiv-transport (factorization s) es)
```
