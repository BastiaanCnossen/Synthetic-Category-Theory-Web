# Symmetry of pullbacks

The comparison swaps the two projections and reverses the matching
isomorphism. Applying it twice gives the identity by the cone calculus.
This proves the symmetry part of `exercise:Associativity_Fiber_Products`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.PullbackSymmetry
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P using (IsPullback)

pullbackSwap : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  MAP (Pullback f g) (Pullback g f)
pullbackSwap f g = pbLift (coneSwap (pbCone f g))

pullbackSwap-swap : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  NatIso (pullbackSwap g f ∘ pullbackSwap f g) (id (Pullback f g))
pullbackSwap-swap f g = pullback-reflect _ _
  (coneIso-compose (coneIso-inverse (conePre-id (pbCone f g)))
    (coneIso-compose (coneSwap-swap (pbCone f g))
    (coneIso-compose (coneIso-swap (pbLift-β (coneSwap (pbCone f g))))
    (coneIso-compose (coneSwap-pre (pullbackSwap f g) (pbCone g f))
    (coneIso-compose (coneIso-pre (pullbackSwap f g) (pbLift-β (coneSwap (pbCone g f))))
      (coneIso-inverse (conePre-assoc (pullbackSwap f g) (pullbackSwap g f) (pbCone f g))))))))

pullbackSwap-isEquiv : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  IsEquiv (pullbackSwap f g)
pullbackSwap-isEquiv f g = record
  { inverse = pullbackSwap g f
  ; sectionIso = invIso (pullbackSwap-swap f g)
  ; retractionIso = invIso (pullbackSwap-swap g f) }

pullbackSwap-factorization : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → NatIso (pbLift (coneSwap s)) (pullbackSwap f g ∘ pbLift s)
pullbackSwap-factorization {f = f} {g} s = pullback-reflect _ _
  (coneIso-compose (coneIso-inverse image) (pbLift-β (coneSwap s)))
  where
  image = coneIso-compose (coneIso-swap (pbLift-β s))
    (coneIso-compose (coneSwap-pre (pbLift s) (pbCone f g))
    (coneIso-compose (coneIso-pre (pbLift s) (pbLift-β (coneSwap (pbCone f g))))
      (coneIso-inverse (conePre-assoc (pbLift s) (pullbackSwap f g) (pbCone g f)))))

pullback-swap : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → IsPullback s → IsPullback (coneSwap s)
pullback-swap {f = f} {g} s es = equiv-transport (invIso (pullbackSwap-factorization s))
  (equiv-compose (pbLift s) (pullbackSwap f g) es (pullbackSwap-isEquiv f g))

pullback-equivalenceʳ : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  IsEquiv f → IsEquiv (pb₂ {f = f} {g})
pullback-equivalenceʳ f g ef = equiv-transport (pbLift-β₁ (coneSwap (pbCone f g)))
  (equiv-compose (pullbackSwap f g) pb₁ (pullbackSwap-isEquiv f g)
    (pullback-equivalence g f ef))

pullback-unitˡ : {C E : CAT} (f : MAP C E) → IsEquiv (pb₁ {f = f} {id E})
pullback-unitˡ {E = E} f = pullback-equivalence f (id E) (id-isEquiv E)

pullback-unitʳ : {C E : CAT} (f : MAP C E) → IsEquiv (pb₂ {f = id E} {f})
pullback-unitʳ {E = E} f = pullback-equivalenceʳ (id E) f (id-isEquiv E)
```
