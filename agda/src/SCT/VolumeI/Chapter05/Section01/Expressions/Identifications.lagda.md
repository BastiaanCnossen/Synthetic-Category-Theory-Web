# Identification expressions

The syntax records identities, inversion, vertical and horizontal composition, associators, and unitors with their functor-expression boundaries. Interpretation keeps these boundaries and their parenthesization.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Expressions.Identifications where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors

module Cells {l : Level} (G : Signature l) where
  open Signature G
  open Syntax G
  -- A shared typed syntax, interpreted in any copy of Theory. No quotient
  -- identifies different bracketings, coherence witnesses, or derivations.
  data Iso : {A B : Object} → Fun A B → Fun A B → Set l where
    identity-cell : {A B : Object} (X : Fun A B) → Iso X X
    vertical : {A B : Object} {X Y Z : Fun A B} → Iso Y Z → Iso X Y → Iso X Z
    inverse : {A B : Object} {X Y : Fun A B} → Iso X Y → Iso Y X
    horizontal : {A B C : Object} {X X' : Fun A B} {Y Y' : Fun B C}
      → Iso Y Y' → Iso X X' → Iso (compose Y X) (compose Y' X')
    post : {A B C : Object} {X X' : Fun A B} (Y : Fun B C)
      → Iso X X' → Iso (compose Y X) (compose Y X')
    pre : {A B C : Object} {Y Y' : Fun B C} → Iso Y Y' → (X : Fun A B)
      → Iso (compose Y X) (compose Y' X)
    associator : {A B C D : Object} (X : Fun A B) (Y : Fun B C) (Z : Fun C D)
      → Iso (compose (compose Z Y) X) (compose Z (compose Y X))
    left-unit : {A B : Object} (X : Fun A B) → Iso (compose (identity B) X) X
    right-unit : {A B : Object} (X : Fun A B) → Iso (compose X (identity A)) X

module Interpret {l : Level} {G : Signature l} {T : Theory l l l} (I : Interpretation G T) where
  private
    module T = View T
  open Signature G
  open Syntax G
  open Cells G
  open Evaluate I
  evaluate-cell : {A B : Object} {X Y : Fun A B} → Iso X Y → T._=₁_ (evaluate X) (evaluate Y)
  evaluate-cell (identity-cell X) = T.idIso (evaluate X)
  evaluate-cell (vertical q p) = T._∙_ (evaluate-cell q) (evaluate-cell p)
  evaluate-cell (inverse p) = T._⁻¹ (evaluate-cell p)
  evaluate-cell (horizontal q p) = T._⋆_ (evaluate-cell q) (evaluate-cell p)
  evaluate-cell (post Y p) = T._◁_ (evaluate Y) (evaluate-cell p)
  evaluate-cell (pre p X) = T._▷_ (evaluate-cell p) (evaluate X)
  evaluate-cell (associator X Y Z) = T.comp-assoc (evaluate X) (evaluate Y) (evaluate Z)
  evaluate-cell (left-unit X) = T.comp-unitˡ (evaluate X)
  evaluate-cell (right-unit X) = T.comp-unitʳ (evaluate X)
```
