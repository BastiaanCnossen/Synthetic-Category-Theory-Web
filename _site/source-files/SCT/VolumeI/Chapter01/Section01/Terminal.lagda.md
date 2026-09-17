# The terminal category

This is the supplied structure of `post:Terminal_Category`. `One` was introduced
with the vocabulary so that absolute objects and natural isomorphisms could be
defined before stating universal properties.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary

module SCT.VolumeI.Chapter01.Section01.Terminal
  {c m a : Level} (V : Vocabulary c m a) where

open Vocabulary V

record TerminalStructure : Set (c ⊔ m) where
  field
    terminate : (C : CAT) → MAP C One
    terminalIso-isEquiv : {T : CAT} (f g : MAP T One)
      → IsEquiv (terminate (f ≅ g))

module Constructions (T : TerminalStructure) where
  open TerminalStructure T

  const : {P C : CAT} → ObjAbs C → MAP P C
  const {P} x = x ∘ terminate P

  IsContractible : CAT → Set m
  IsContractible C = IsEquiv (terminate C)

  terminal-iso : {P : CAT} (f g : MAP P One) → NatIso f g
  terminal-iso f g = IsEquiv.inverse (terminalIso-isEquiv f g)
```

`terminal-iso` is a proved construction: the inverse supplied by the terminal
axiom is precisely a functor from `One` to the required isomorphism anima.
