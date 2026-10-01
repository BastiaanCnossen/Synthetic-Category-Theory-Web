# Changes of contextual theories

A change has an underlying assignment, operation comparisons, and
preservation of the specified basic coherences. Weakening is such a
change. A change also acts on a further anima context, as in
`con:Preservation_Of_Contextual_Structure`.

The codes distinguish changes from their realizations. No equality or
composition rule for changes is imposed. Later preservation records are
indexed by every change, including its lifts to further contexts.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening; compose)
open import SCT.VolumeI.Chapter05.Section01.PrimitivePreservation using (PrimitiveWeakening)
import SCT.VolumeI.Chapter05.Section01.Routes as Routes

module SCT.VolumeI.Chapter05.Section01.Changes
  {l : Level} (C : ContextualTheories l) where

open ContextualTheories C

record Changes : Set (lsuc l) where
  field
    Change : Context → Context → Set l
    realization : {Γ Δ : Context} → Change Γ Δ → PrimitiveWeakening (at Γ) (at Δ)

  underlying : {Γ Δ : Context} → Change Γ Δ → Weakening (at Γ) (at Δ)
  underlying w = PrimitiveWeakening.weakening (realization w)

  image-anima : {Γ Δ : Context} → Change Γ Δ → In.AN Γ → In.AN Δ
  image-anima {Γ} {Δ} w A = record
    { category = Weakening.cat (underlying w) (In.AN.category {Γ = Γ} A)
    ; witness = Weakening.anima (underlying w) (In.AN.witness {Γ = Γ} A) }

  field
    weakening : (Γ : Context) (A : In.AN Γ) → Change Γ (extend Γ A)
    lift : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Change (extend Γ A) (extend Δ (image-anima w A))

-- These fields specify the category, functor, and identification-anima
-- layers of the lifting comparison. Preservation of its higher chosen
-- witnesses is a further part of the chapter's general scheme.
record LiftComparisons (D : Changes) : Set l where
  open Changes D
  field
    weakening-comparison : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Routes.Comparison
        (compose (underlying (lift w A)) (underlying (weakening Γ A)))
        (compose (underlying (weakening Δ (image-anima w A))) (underlying w))
    weakening-paths : {Γ Δ : Context} (w : Change Γ Δ) (A : In.AN Γ)
      → Routes.PathCompatibility (weakening-comparison w A)
```
