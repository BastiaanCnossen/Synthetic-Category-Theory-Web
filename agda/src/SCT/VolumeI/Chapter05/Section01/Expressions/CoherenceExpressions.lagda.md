# Pentagon and triangle expressions

These templates contain the short and long paths of the primitive pentagon and triangle. They are syntax, with exactly the parenthesization and horizontal composites of the axioms.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors
open import SCT.VolumeI.Chapter05.Section01.Expressions.Identifications

module SCT.VolumeI.Chapter05.Section01.Expressions.CoherenceExpressions {l : Level} (G : Signature l) where
open Signature G
open Syntax G
open Cells G

module Pentagon {a b c d e : Object} (f : Fun a b) (g : Fun b c) (h : Fun c d) (k : Fun d e) where
  left = compose (compose (compose k h) g) f
  right = compose k (compose h (compose g f))
  short long : Iso left right
  short = vertical (associator (compose g f) h k) (associator f g (compose k h))
  long = vertical (vertical (horizontal (identity-cell k) (associator f g h))
      (associator f (compose h g) k))
    (horizontal (associator g h k) (identity-cell f))

module Triangle {a b c : Object} (f : Fun a b) (g : Fun b c) where
  left = compose (compose g (identity b)) f
  right = compose g f
  short long : Iso left right
  short = horizontal (right-unit g) (identity-cell f)
  long = vertical (horizontal (identity-cell g) (left-unit f)) (associator f (identity b) g)

-- These templates contain only syntax. Their interpretations retain the
-- literal parentheses and horizontal composites of the primitive axioms.
```
