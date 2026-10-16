# Pullback squares along embeddings

A commuting square with an equivalence on its left leg and an embedding on
its right cospan arrow is a pullback. The actual pullback factor and its
projection triangle give a section of the first projection, using the given
inverse of the left leg. Base change makes that projection an embedding, so
its section makes it an equivalence. Cancellation proves universality.

For a map of cospans whose endpoint maps are equivalences and whose base map
is an embedding, this criterion makes the original right square cartesian.
The existing cartesian-cospan comparison then gives an equivalence of the
actual induced pullback map, retaining its specified matching.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.EmbeddingPullbackSquares where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (Section; equiv-transport; equiv-cancel-left)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
  using (Pullback; pullback₁; pullback-factor; pullback-factor-β₁)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.Embeddings
  using (IsEmbedding; chosen-base-change-embedding; embedding-with-section)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality
  using (CospanMap; cospan-right-cone; pullback-map; module CospanCartesian)

module _ {Γ : Context} where
  isPullback-from-left-isEquiv-and-embedding : {C D E T : CAT Γ}
    {h : MAP C E} {e : MAP D E} (t : Cone h e T)
    → IsEmbedding e → IsEquiv (Cone.left t) → IsPullback t
  isPullback-from-left-isEquiv-and-embedding {C} {D} {E} {T} {h} {e} t ee ev =
    equiv-cancel-left pullback-lift p projection-equivalence (equiv-transport (β ⁻¹) ev)
    where
      Q : CAT Γ
      Q = Pullback h e
      p : MAP Q C
      p = pullback₁ {f = h} {g = e}
      pullback-lift : MAP T Q
      pullback-lift = pullback-factor t
      v : MAP T C
      v = Cone.left t
      z : MAP C T
      z = IsEquiv.inverse ev
      β : (p ∘ pullback-lift) =₁ v
      β = pullback-factor-β₁ t

      projection-embedding : IsEmbedding p
      projection-embedding = chosen-base-change-embedding h e ee
      projection-section : Section p
      projection-section = record
        { section = pullback-lift ∘ z
        ; section-law = comp-assoc z pullback-lift p ∙
            ((β ⁻¹ ▷ z) ∙ IsEquiv.right-inverse-law ev) }
      projection-equivalence : IsEquiv p
      projection-equivalence = embedding-with-section p projection-embedding projection-section

  cospan-embedding-isEquiv : {C D E C′ D′ E′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    (F : CospanMap f g f′ g′)
    → IsEquiv (CospanMap.left F) → IsEquiv (CospanMap.right F)
    → IsEmbedding (CospanMap.base F) → IsEquiv (pullback-map F)
  cospan-embedding-isEquiv F eu ev ew = CospanCartesian.pullback-map-isEquiv F eu
    (isPullback-from-left-isEquiv-and-embedding (cospan-right-cone F) ew ev)
```
