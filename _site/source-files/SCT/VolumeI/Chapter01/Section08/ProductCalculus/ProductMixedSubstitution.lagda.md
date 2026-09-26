# Moving a parameter past two restrictions

Moving `h` past a composite functor agrees with moving it past the two
functors successively. The comparison refers to the specified product
compositors and separation isomorphisms. Its two projection calculations
were proved separately, so product extensionality completes the proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductFirstCoordinate as First
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate as Second
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterFirstCoordinate as ParameterFirst
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate as ParameterSecond

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductMixedSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality)

abstract
  separate-composition : {X Y A B C : CAT} (h : MAP X Y) (f : MAP A B) (g : MAP B C) →

      ((productRestriction-comp Y f g ▷ productMap h (id A)) ∙
        paste ((productMap-separate h g) ⁻¹) ((productMap-separate h f) ⁻¹)) =₂
      ((productMap-separate h (g ∘ f)) ⁻¹ ∙
        (productMap h (id C) ◁ productRestriction-comp X f g))
  separate-composition h f g = pair-iso-extensionality
    (First.Mixed.comparison 𝒯 M h f g) (Second.Mixed.comparison 𝒯 M h f g)

  separate-substitution : {X Y Z A B : CAT} (h : MAP X Y) (k : MAP Y Z) (f : MAP A B) →

      (productMap-separate (k ∘ h) f ∙
        (productRestriction Z f ◁ slice-comparison {C = A} k h)) =₂
      ((slice-comparison {C = B} k h ▷ productRestriction X f) ∙
        paste (productMap-separate k f) (productMap-separate h f))
  separate-substitution h k f = pair-iso-extensionality
    (ParameterFirst.Mixed.comparison 𝒯 M h k f)
    (ParameterSecond.Mixed.comparison 𝒯 M h k f)
```
