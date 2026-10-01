# Functor expressions and their comparisons

A typed signature describes the input tuple. Identity and composition expressions are interpreted in each theory, and recursion constructs the comparison between a weakened expression and its interpretation on weakened inputs.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Expressions.Functors where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)

-- The object and arrow variables of an input tuple, with their typing.
record Signature (l : Level) : Set (lsuc l) where
  field
    Object : Set l
    Arrow : Object → Object → Set l

module Syntax {l : Level} (G : Signature l) where
  open Signature G
  data Fun : Object → Object → Set l where
    atom : {A B : Object} → Arrow A B → Fun A B
    identity : (A : Object) → Fun A A
    compose : {A B C : Object} → Fun B C → Fun A B → Fun A C

record Interpretation {l : Level} (G : Signature l) (T : Theory l l l) : Set l where
  private
    module G = Signature G
    module T = View T
  field
    object : G.Object → T.CAT
    arrow : {A B : G.Object} → G.Arrow A B → T.MAP (object A) (object B)

module Evaluate {l : Level} {G : Signature l} {T : Theory l l l} (I : Interpretation G T) where
  private
    module T = View T
  open Signature G
  open Syntax G
  open Interpretation I
  evaluate : {A B : Object} → Fun A B → T.MAP (object A) (object B)
  evaluate (atom f) = arrow f
  evaluate (identity A) = T.id (object A)
  evaluate (compose g f) = T._∘_ (evaluate g) (evaluate f)

image : {l : Level} {G : Signature l} {S T : Theory l l l}
  → Weakening S T → Interpretation G S → Interpretation G T
image W I = record
  { object = λ A → Weakening.cat W (Interpretation.object I A)
  ; arrow = λ f → Weakening.map W (Interpretation.arrow I f) }

module Compare {l : Level} {G : Signature l} {S T : Theory l l l}
  (W : Weakening S T) (I : Interpretation G S) where
  private
    module T = View T
    module S = Evaluate I
    module J = Evaluate (image W I)
  open Signature G
  open Syntax G
  open Weakening W
  comparison : {A B : Object} (X : Fun A B) → T._=₁_ (map (S.evaluate X)) (J.evaluate X)
  comparison (atom f) = T.idIso _
  comparison (identity A) = unit (Interpretation.object I A)
  comparison (compose Y X) = T._∙_ (T._⋆_ (comparison Y) (comparison X)) (comp (S.evaluate X) (S.evaluate Y))
```
