# Terms and absolute objects

This is the term convention of `def:Term`.
A term is the corresponding functor; substitution is external composition.
The universal term is the identity functor, not additional universal-property
data. In particular, this file adds no new axioms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary

module SCT.VolumeI.Chapter01.Section01.Terms
  {c m a : Level} (V : Vocabulary c m a) where

open Vocabulary V

Term : CAT → CAT → Set m
Term = MAP

universalTerm : (C : CAT) → Term C C
universalTerm = id

substitute : {B C D : CAT} → Term C D → MAP B C → Term B D
substitute = _∘_
```

`Obj-abs C = MAP One C` is defined in `Vocabulary`. The future name `Obj` is
reserved for objects parameterized by an anima. A term can have any categorical
source; it is not automatically an object in that proposed restricted sense.

For `f g : MAP X C`, an identification between the whole expressions is
`f =₁ g`. A functor into the fixed anima `(f ＝ g)` is a different term,
whose target is that anima. These two uses of parameters are kept distinct.
