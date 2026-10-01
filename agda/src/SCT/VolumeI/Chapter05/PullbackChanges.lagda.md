# Pullback preservation for changes of context

The total-category comparison for substitution uses preservation of
pullbacks by the substitution and by weakening to its target context.
The type below isolates exactly this constructor-preservation input.
It is supplied by the corresponding field of Preservation, but the
substitution theorems do not require that larger certificate package.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
import SCT.VolumeI.Chapter05.Theory as ContextTheory
import SCT.VolumeI.Chapter05.Section01.PullbackPreservation as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter05.PullbackChanges
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D) where

open ContextualTheories C
open Changes.Changes D
open ContextTheory.ContextualConstructions K

Preservation : Set l
Preservation = {Γ Δ : Context} (w : Change Γ Δ)
  → Pullbacks.PreservesPullbacks (underlying {Γ} {Δ} w)
    (Laws.PullbackStructure.dataPullback (pullbacks Γ))
    (Laws.PullbackStructure.dataPullback (pullbacks Δ))
```
