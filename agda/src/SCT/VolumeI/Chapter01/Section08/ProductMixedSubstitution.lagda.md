# Moving a parameter past two restrictions

Moving `h` past a composite functor agrees with moving it past the two
functors successively. The comparison refers to the specified product
compositors and separation isomorphisms. Its two projection calculations
were proved separately, so product extensionality completes the proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section08.ProductFirstCoordinate as First
import SCT.VolumeI.Chapter01.Section08.ProductSecondCoordinate as Second
import SCT.VolumeI.Chapter01.Section08.ParameterFirstCoordinate as ParameterFirst
import SCT.VolumeI.Chapter01.Section08.ParameterSecondCoordinate as ParameterSecond

module SCT.VolumeI.Chapter01.Section08.ProductMixedSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M using (slice-comparison)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality)

abstract
  separate-composition : {X Y A B C : CAT} (h : MAP X Y) (f : MAP A B) (g : MAP B C) →
    Iso₂
      ((productRestriction-comp Y f g ▷ productMap h (id A)) ∙
        paste (invIso (productMap-separate h g)) (invIso (productMap-separate h f)))
      (invIso (productMap-separate h (g ∘ f)) ∙
        (productMap h (id C) ◁ productRestriction-comp X f g))
  separate-composition h f g = pair-iso-extensionality
    (First.Mixed.comparison 𝒯 M h f g) (Second.Mixed.comparison 𝒯 M h f g)

  separate-substitution : {X Y Z A B : CAT} (h : MAP X Y) (k : MAP Y Z) (f : MAP A B) →
    Iso₂
      (productMap-separate (k ∘ h) f ∙
        (productRestriction Z f ◁ slice-comparison {C = A} k h))
      ((slice-comparison {C = B} k h ▷ productRestriction X f) ∙
        paste (productMap-separate k f) (productMap-separate h f))
  separate-substitution h k f = pair-iso-extensionality
    (ParameterFirst.Mixed.comparison 𝒯 M h k f)
    (ParameterSecond.Mixed.comparison 𝒯 M h k f)
```
