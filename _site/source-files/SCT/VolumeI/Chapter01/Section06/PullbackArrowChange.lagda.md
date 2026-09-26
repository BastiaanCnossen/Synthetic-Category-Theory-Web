# Pullbacks and isomorphic cospan arrows

Replacing a cospan arrow by a specified naturally isomorphic functor
preserves pullback squares. The comparison uses that specified isomorphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.PullbackArrowChange
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P

module ChangeLeft {C D E : CAT} {f f′ : MAP C E} (α : f =₁ f′) (g : MAP D E) where

  source = pullbackCone f g
  target = pullbackCone f′ g
  forward = pullbackLift (changeLeft α source)
  backward = pullbackLift (changeLeft (α ⁻¹) target)

  backward-forward : (backward ∘ forward) =₁ (id (Pullback f g))
  backward-forward = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id source))
    (coneIso-compose (changeLeft-back α source)
    (coneIso-compose (changeLeft-iso (α ⁻¹) (pullbackLift-β (changeLeft α source)))
    (coneIso-compose (changeLeft-pre (α ⁻¹) forward target)
    (coneIso-compose (coneIso-pre forward (pullbackLift-β (changeLeft (α ⁻¹) target)))
      (coneIso-inverse (conePre-assoc forward backward source)))))))

  forward-backward : (forward ∘ backward) =₁ (id (Pullback f′ g))
  forward-backward = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id target))
    (coneIso-compose (changeLeft-backʳ α target)
    (coneIso-compose (changeLeft-iso α (pullbackLift-β (changeLeft (α ⁻¹) target)))
    (coneIso-compose (changeLeft-pre α backward source)
    (coneIso-compose (coneIso-pre backward (pullbackLift-β (changeLeft α source)))
      (coneIso-inverse (conePre-assoc backward forward target)))))))

  forward-isEquiv : IsEquiv forward
  forward-isEquiv = record
    { inverse = backward ; sectionIso = backward-forward ⁻¹ ; retractionIso = forward-backward ⁻¹ }

  factorization : {T : CAT} (s : Cone f g T) →
    (pullbackLift (changeLeft α s)) =₁ (forward ∘ pullbackLift s)
  factorization s = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse image) (pullbackLift-β (changeLeft α s)))
    where
    image = coneIso-compose (changeLeft-iso α (pullbackLift-β s))
      (coneIso-compose (changeLeft-pre α (pullbackLift s) source)
      (coneIso-compose (coneIso-pre (pullbackLift s) (pullbackLift-β (changeLeft α source)))
        (coneIso-inverse (conePre-assoc (pullbackLift s) forward target))))

  preserve : {T : CAT} (s : Cone f g T) → IsPullback s → IsPullback (changeLeft α s)
  preserve s es = equiv-transport ((factorization s) ⁻¹)
    (equiv-compose (pullbackLift s) forward es forward-isEquiv)

  reflect : {T : CAT} (s : Cone f g T) → IsPullback (changeLeft α s) → IsPullback s
  reflect s es = equiv-cancel-left (pullbackLift s) forward forward-isEquiv
    (equiv-transport (factorization s) es)
```
