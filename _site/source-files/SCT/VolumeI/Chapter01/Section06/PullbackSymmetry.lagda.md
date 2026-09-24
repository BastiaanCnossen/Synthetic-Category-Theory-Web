# Symmetry of pullbacks

The comparison swaps the two projections and reverses the matching
isomorphism. Applying it twice gives the identity by the cone calculus.
This proves the symmetry part of `exercise:Associativity_Fiber_Products`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.PullbackSymmetry
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackLifting 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)

pullbackSwap : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  MAP (Pullback f g) (Pullback g f)
pullbackSwap f g = pullbackLift (coneSwap (pullbackCone f g))

pullbackSwap-swap : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  (pullbackSwap g f ∘ pullbackSwap f g) =₁ (id (Pullback f g))
pullbackSwap-swap f g = pullback-reflect _ _
  (coneIso-compose (coneIso-inverse (conePre-id (pullbackCone f g)))
    (coneIso-compose (coneSwap-swap (pullbackCone f g))
    (coneIso-compose (coneIso-swap (pullbackLift-β (coneSwap (pullbackCone f g))))
    (coneIso-compose (coneSwap-pre (pullbackSwap f g) (pullbackCone g f))
    (coneIso-compose (coneIso-pre (pullbackSwap f g) (pullbackLift-β (coneSwap (pullbackCone g f))))
      (coneIso-inverse (conePre-assoc (pullbackSwap f g) (pullbackSwap g f) (pullbackCone f g))))))))

pullbackSwap-isEquiv : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  IsEquiv (pullbackSwap f g)
pullbackSwap-isEquiv f g = record
  { inverse = pullbackSwap g f
  ; sectionIso = (pullbackSwap-swap f g) ⁻¹
  ; retractionIso = (pullbackSwap-swap g f) ⁻¹ }

pullbackSwap-factorization : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → (pullbackLift (coneSwap s)) =₁ (pullbackSwap f g ∘ pullbackLift s)
pullbackSwap-factorization {f = f} {g} s = pullback-reflect _ _
  (coneIso-compose (coneIso-inverse image) (pullbackLift-β (coneSwap s)))
  where
  image = coneIso-compose (coneIso-swap (pullbackLift-β s))
    (coneIso-compose (coneSwap-pre (pullbackLift s) (pullbackCone f g))
    (coneIso-compose (coneIso-pre (pullbackLift s) (pullbackLift-β (coneSwap (pullbackCone f g))))
      (coneIso-inverse (conePre-assoc (pullbackLift s) (pullbackSwap f g) (pullbackCone g f)))))

pullback-swap : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → IsPullback s → IsPullback (coneSwap s)
pullback-swap {f = f} {g} s es = equiv-transport ((pullbackSwap-factorization s) ⁻¹)
  (equiv-compose (pullbackLift s) (pullbackSwap f g) es (pullbackSwap-isEquiv f g))

pullback-equivalenceʳ : {C D E : CAT} (f : MAP C E) (g : MAP D E) →
  IsEquiv f → IsEquiv (pullback₂ {f = f} {g})
pullback-equivalenceʳ f g ef = equiv-transport (pullbackLift-β₁ (coneSwap (pullbackCone f g)))
  (equiv-compose (pullbackSwap f g) pullback₁ (pullbackSwap-isEquiv f g)
    (pullback-equivalence g f ef))

pullback-unitˡ : {C E : CAT} (f : MAP C E) → IsEquiv (pullback₁ {f = f} {id E})
pullback-unitˡ {E = E} f = pullback-equivalence f (id E) (id-isEquiv E)

pullback-unitʳ : {C E : CAT} (f : MAP C E) → IsEquiv (pullback₂ {f = id E} {f})
pullback-unitʳ {E = E} f = pullback-equivalenceʳ (id E) f (id-isEquiv E)
```
