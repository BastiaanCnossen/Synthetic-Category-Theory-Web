# Theories in anima contexts

An ambient context selects a copy of the basic theory. Extending it by an
anima selects another copy. In particular, extending the absolute context
by its terminal anima is not a computation rule for the absolute theory.
Every subsequent contextual structure is indexed by all these contexts,
so its relative instances have exactly the same types as its absolute one.

This record supplies the indexing and the basic vocabulary. Additional
axioms, including weakening and dependent products, are separate records.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Contexts where

open import SCT.VolumeI.Chapter05.Section01.Prelude

record ContextualTheories (l : Level) : Set (lsuc l) where
  field
    Context : Set l
    at : Context → Theory l l l
    absolute : Context
    extend : (Γ : Context) → View.AN (at Γ) → Context

  module In (Γ : Context) = View (at Γ)

  Absolute : Theory l l l
  Absolute = at absolute

  Local : (Γ : Context) → In.AN Γ → Theory l l l
  Local Γ A = at (extend Γ A)
```
