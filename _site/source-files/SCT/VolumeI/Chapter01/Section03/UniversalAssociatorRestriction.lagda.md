# Restricting the universal associator

The universal associator is defined on the product of three mapping
animae. Its restriction to any common anima parameter agrees with the
associator lifted directly there. The comparison uses the four proved
composition squares, followed by reflection through retained evaluation.
Thus it compares the specified associators themselves.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as Internal
import SCT.VolumeI.Chapter01.Section03.UniversalCoherence as Universal
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange as CompositionChange

module SCT.VolumeI.Chapter01.Section03.UniversalAssociatorRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open Internal 𝒯 M
open Universal 𝒯 M using (module AssocRestriction; module AssociatorChange)
open CompositionChange 𝒯 M using (retained-compose-parameter-change)

opaque
  universal-assoc : {P A B C D : CAT} (pAn : isAn P)
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → =₂ (internalAssoc h g f) (compose-assoc pAn h g f)
  universal-assoc {P} {A} {B} {C} {D} pAn h g f =
    let module U = AssocRestriction {Q = P} {A = A} {B = B} {C = C} {D = D} h g f
        module R = AssociatorChange {P = U.P} {Q = P} {A = A} {B = B} {C = C} {D = D}
          U.point U.universal-h U.universal-g U.universal-f
          U.first U.second U.third
    in U.from-route-square pAn
      (R.route
        (retained-compose-parameter-change U.universal-h U.universal-g U.point)
        (retained-compose-parameter-change U.universal-g U.universal-f U.point)
        (retained-compose-parameter-change
          (composeTerm U.universal-h U.universal-g) U.universal-f U.point)
        (retained-compose-parameter-change
          U.universal-h (composeTerm U.universal-g U.universal-f) U.point))
```
