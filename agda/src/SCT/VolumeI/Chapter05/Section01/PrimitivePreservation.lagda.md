# Preservation of the chosen basic witnesses

The record assembles the 22 identification-valued generator families of the basic comparison package. It includes the selected pentagon and triangle witnesses. Constructor universal properties and compatibility with composite changes are separate requirements.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.PrimitivePreservation where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
open import SCT.VolumeI.Chapter05.Section01.ChosenCoherences using (ChosenCoherences)
open import SCT.VolumeI.Chapter05.Section01.ChosenVertical using (ChosenVertical)
open import SCT.VolumeI.Chapter05.Section01.ChosenWhiskering using (ChosenWhiskering)
open import SCT.VolumeI.Chapter05.Section01.ChosenHorizontal using (ChosenHorizontal)
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ProductWitnesses as ProductWitnesses

-- Covers all 22 identification-valued generator families in the inventory.
-- It does not claim closure under canonical composition, indexed naturality,
-- or preservation of the selected universal-property equivalence certificates.
record PrimitivePreservation {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) : Set l where
  field
    vertical : ChosenVertical W K
    whiskering : ChosenWhiskering W K
    horizontal : ChosenHorizontal W K
    pentagonTriangle : ChosenCoherences W K
  -- Identity, associator and unitors are already required by K.
  -- The two product beta comparisons require no further field.
  open ProductWitnesses W public using (beta₁; beta₂)

record PrimitiveWeakening {l : Level} (S T : Theory l l l) : Set l where
  field
    weakening : Weakening S T
    operations : OperationCompatibility weakening
    preservation : PrimitivePreservation weakening operations
```
