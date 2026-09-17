# The canonical empty pullback square

This is `lem:Canonical_Pullback_Square`. Strictness makes the projection to
the initial category an equivalence, and two-out-of-three applies to the
chosen factorization of any cone with initial vertex and initial left leg.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Initial as Initial
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.InitialPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (I : Initial.InitialStructure 𝒯 M) (S : Initial.StrictInitial 𝒯 M I)
  (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯 M
open Initial.Initiality 𝒯 M I
open Initial.StrictInitial S
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P

initial-cone-isPullback : {D E : CAT} {f : MAP Zero E} {g : MAP D E}
  (s : Cone f g Zero) → IsPullback s
initial-cone-isPullback s = equiv-cancel-left (pbLift s) pb₁ (into-zero-isEquiv pb₁)
  (into-zero-isEquiv (pb₁ ∘ pbLift s))

initialCone : {D E : CAT} (g : MAP D E) → Cone (initiate E) g Zero
initialCone g = record
  { left = id Zero ; right = initiate _ ; match = initial-iso _ _ }

initial-square : {D E : CAT} (g : MAP D E) → IsPullback (initialCone g)
initial-square g = initial-cone-isPullback (initialCone g)
```
