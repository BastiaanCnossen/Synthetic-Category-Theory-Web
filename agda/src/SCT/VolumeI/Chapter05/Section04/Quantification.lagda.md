# Quantification after substitution

The final convention of Chapter 5 includes diagrams after every further
substitution. `Diagram` retains that further base and its map to the
original base. Thus a shape in `Diagram` belongs to the new context; it
need not be the weakening of an absolute category.

The record only displays the scope of this quantification. It does not
define colimits or assert that their existence is stable under a change
of context. Such properties can be supplied as `Property` below.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Contexts
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Changes as Changes
import SCT.VolumeI.Chapter05.Theory as ContextTheory
import SCT.VolumeI.Chapter05.Section04.Substitution as Substitution

module SCT.VolumeI.Chapter05.Section04.Quantification
  {l : Level} (C : ContextualTheories l) (D : Changes.Changes C)
  (K : ContextTheory.ContextualConstructions C D) (Γ : ContextualTheories.Context C)
  (R : Substitution.At.Substitution C D K Γ) where

open ContextualTheories C
module R = Substitution.At.Substitution R
private
  module S = View (at Γ)

module Over (A : S.AN) (X : In.CAT (extend Γ A))
  (Shape : (Δ : Context) → In.CAT Δ → Set l) where

  record Diagram : Set l where
    field
      base : S.AN
      substitution : S.MAP (S.AN.category base) (S.AN.category A)
      shape : In.CAT (extend Γ base)
      admissible : Shape (extend Γ base) shape
      functor : In.MAP (extend Γ base) shape
        (Weakening.cat (R.pull {A} {base} substitution) X)

  Contextually : (Diagram → Set l) → Set l
  Contextually Property = (diagram : Diagram) → Property diagram

  specialize : {Property : Diagram → Set l} → Contextually Property
    → (B : S.AN) (g : S.MAP (S.AN.category B) (S.AN.category A))
    → (I : In.CAT (extend Γ B)) (i : Shape (extend Γ B) I)
    → (f : In.MAP (extend Γ B) I (Weakening.cat (R.pull {A} {B} g) X))
    → Property (record { base = B ; substitution = g ; shape = I ; admissible = i ; functor = f })
  specialize property B g I i f = property _
```
