# The Rezk axiom and its fiber consequences

The existing manuscript clause axiom:C_Rezk_Axiom asserts that the actual
identity-isomorphism functor is an equivalence. Its target is the accepted
iterated pullback Iso C and its map is the accepted constant-triangle
factorization. No replacement isomorphism category or additional witness
is assumed.

The concrete fiber and natural-isomorphism interfaces below specialize the
already checked conditional owners. Their complete computation laws,
including every chosen cone matching and naming recovery, are retained.
The identity-arrow functor is an embedding by the conditional isomorphism
embedding theorem and this actual Rezk equivalence.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section03.RezkAxiom where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms using (identityIso)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (identityArrow)
open import SCT.VolumeI.Chapter01.Section06.Embeddings using (IsEmbedding)
import SCT.VolumeI.Chapter02.Section03.IsomorphismEmbedding as ConditionalEmbedding
import SCT.VolumeI.Chapter02.Section03.RezkFibers as ConditionalFibers
import SCT.VolumeI.Chapter02.Section03.NaturalIsomorphisms as ConditionalNatural
open ConditionalFibers public using (IsoBetween)
open ConditionalNatural public using (NatIsoBetween)

module _ {Γ : Context} where
  postulate
    rezk-isEquiv : (C : CAT Γ) → IsEquiv (identityIso C)

  identityArrow-isEmbedding : (C : CAT Γ) → IsEmbedding (identityArrow {C = C})
  identityArrow-isEmbedding C = ConditionalEmbedding.identityArrow-isEmbedding C (rezk-isEquiv C)

  module IdentificationFiber {C : CAT Γ} (x y : MAP One C) =
    ConditionalFibers.IdentificationFiber C (rezk-isEquiv C) x y

  module NaturalIdentification {C D : CAT Γ} (f g : MAP C D) =
    ConditionalNatural.NaturalIdentification (rezk-isEquiv (Fun C D)) f g
```
