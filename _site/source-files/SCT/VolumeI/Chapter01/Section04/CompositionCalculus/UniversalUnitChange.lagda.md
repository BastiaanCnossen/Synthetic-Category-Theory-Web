# Restricting the universal unit comparisons

The unit comparisons are chosen on a mapping anima and then restricted
along a parameter map. We compare those restrictions with the unit routes
lifted directly at the new parameter. The identity comparison and every
composition comparison used here are the previously specified ones.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as Internal
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalCoherence as Universal
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalUnitCalculus as Calculus
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedCompositionParameterChange as CompositionChange

module SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalUnitChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open Internal 𝒯 M
open Universal 𝒯 M using (module UnitRestriction)
open Calculus 𝒯 M public
open CompositionChange 𝒯 M using (retained-compose-parameter-change)

```

Apply these route squares to the identity functor on the universal
mapping anima. Reflection then identifies the actual normalized universal
unitors with the direct lifts at any anima parameter.

```agda
opaque
  universal-unitˡ : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
    → (internalUnitˡ f) =₂ (compose-unitˡ pAn f)
  universal-unitˡ {C = C} {D} pAn f = UnitRestriction.left-from-route-square f pAn
    (UnitChange.left-route f (id (Map C D)) (comp-unitˡ f)
      (retained-compose-parameter-change (identityTerm D) (id (Map C D)) f))

  universal-unitʳ : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
    → (internalUnitʳ f) =₂ (compose-unitʳ pAn f)
  universal-unitʳ {C = C} {D} pAn f = UnitRestriction.right-from-route-square f pAn
    (UnitChange.right-route f (id (Map C D)) (comp-unitˡ f)
      (retained-compose-parameter-change (id (Map C D)) (identityTerm C) f))
```

