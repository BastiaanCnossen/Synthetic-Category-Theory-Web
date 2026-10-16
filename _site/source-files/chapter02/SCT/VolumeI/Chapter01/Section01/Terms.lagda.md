# Terms in a categorical context

This optional notation leaves Vocabulary's primitives unchanged. A term is
literally a functor from a fixed test category, so it can be used as that
functor without any conversion. Use explicit `MAP` when the source category
has a structural role in the argument.

Usually open `InContext X using (Term; apply)` alongside Vocabulary. To open
the term-formulated `pair` as well, hide Vocabulary's unqualified `pair`;
both definitions denote the same primitive, but their names would be ambiguous.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section01.Terms where

import SCT.VolumeI.Chapter01.Section01.Vocabulary as V
open V hiding (_＝_; pair)

Equal : {Γ : Context} {C D : CAT Γ} → MAP C D → MAP C D → CAT Γ
Equal = V._＝_

module InContext {Γ : Context} (X : CAT Γ) where
  Term : CAT Γ → Set m
  Term C = MAP X C

  apply : {C D : CAT Γ} → MAP C D → Term C → Term D
  apply f x = f ∘ x

  pair : {C D : CAT Γ} → Term C → Term D → Term (C × D)
  pair = V.pair
```

Identification families have their own parameter. Open `InContext X` for
terms and `Equalities A` for identifications when these parameters differ.
The scoped equality below has values in `Set m`; the primitive identification
anima remains `V._＝_`, also available here as `Equal`. When opening the equality
notation, hide the primitive `_＝_` from unqualified imports and use `Equal`
for identification animae. A local `open` alone does not disambiguate the two
operators. Keep the scoped notation out of public re-exports.

```agda
module Equalities {Γ : Context} (A : CAT Γ) where
  infix 10 _＝_

  _＝_ : {C D : CAT Γ} → MAP C D → MAP C D → Set m
  f ＝ g = MAP A (Equal f g)
```

At `A = One` this is definitionally Vocabulary's `=₁`. An identification
between two arbitrary families is still written `=₁`; using the scoped `＝`
there would instead add another family parameter. Ordinary restriction of
a term or an identification family remains precomposition of its underlying
functor. `apply` is ordinary functor application to a term, not an overloaded
operation on equality proofs; whiskering supplies the latter action.
