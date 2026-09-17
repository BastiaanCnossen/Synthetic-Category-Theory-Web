# Contractible categories and contractions

The characterization in `rmk:Characterization_Contractible_Category` is
implemented in both directions. A contraction retains its chosen absolute
object and natural isomorphism; no uniqueness of the witness record is assumed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal

module SCT.VolumeI.Chapter01.Section01.Contractibility
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) where

open Vocabulary V
open Operations V
open Terminal.TerminalStructure T
open Terminal.Constructions V T

record Contraction (C : CAT) : Set m where
  field
    center : ObjAbs C
    contraction : NatIso (const center) (id C)

contractible-to-contraction : {C : CAT} → IsContractible C → Contraction C
contractible-to-contraction e = record
  { center = IsEquiv.inverse e
  ; contraction = invIso (IsEquiv.sectionIso e)
  }

contraction-to-contractible : {C : CAT} → Contraction C → IsContractible C
contraction-to-contractible {C} H = record
  { inverse = Contraction.center H
  ; sectionIso = invIso (Contraction.contraction H)
  ; retractionIso = terminal-iso (id One) (terminate C ∘ Contraction.center H)
  }

terminalIso-contractible : {X : CAT} (f g : MAP X One) → IsContractible (f ≅ g)
terminalIso-contractible = terminalIso-isEquiv
```
