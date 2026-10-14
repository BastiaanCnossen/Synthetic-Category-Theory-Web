# Cancellation along embeddings

An outer pullback and the two supplied embedding hypotheses make the top
cone a pullback. The bottom cone is not assumed to be a pullback. The
section is chosen by Outer.factor with its actual projection computation.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.PullbackCancellation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (factor-through-preWhisker)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
open import SCT.VolumeI.Chapter01.Section06.ConePasting
open import SCT.VolumeI.Chapter01.Section06.Embeddings
```

```agda
module _ {Γ : Context} where
  module Cancellation {C D E D′ E′ C′ : CAT Γ}
    (f : MAP C D) (g : MAP D E) (w : MAP E′ E)
    (bottom : Cone g w D′) (top : Cone f (Cone.left bottom) C′)
    (ev : IsEmbedding (Cone.left bottom)) (ew : IsEmbedding w)
    (outer-isPullback : IsPullback (PasteCones.paste f g bottom top)) where

    module Paste = PasteCones f g bottom
    module Outer = UniversalCone (Paste.paste top) outer-isPullback

    v : MAP D′ D
    v = Cone.left bottom
    u : MAP C′ C
    u = Cone.left top
    p : MAP (Pullback f v) C
    p = pullback₁ {f = f} {v}
    top-factor : MAP C′ (Pullback f v)
    top-factor = pullback-factor top

    projection-isEmbedding : IsEmbedding p
    projection-isEmbedding = chosen-base-change-embedding f v ev
    u-isEmbedding : IsEmbedding u
    u-isEmbedding = base-change-embedding (Paste.paste top) outer-isPullback ew
    top-factor-isEmbedding : IsEmbedding top-factor
    top-factor-isEmbedding = LeftCancellation.cancel top-factor p projection-isEmbedding
      (embedding-cong ((pullback-factor-β₁ top) ⁻¹) u-isEmbedding)

    section : MAP (Pullback f v) C′
    section = Outer.factor (Paste.paste (pullback-cone f v))

    section-projection : (u ∘ section) =₁ p
    section-projection = ConeIdentification₁.left (Outer.β (Paste.paste (pullback-cone f v)))

    section-triangle : (top-factor ∘ section) =₁ (id (Pullback f v))
    section-triangle = embedding-reflect p projection-isEmbedding _ _
      ((comp-unitʳ p) ⁻¹ ∙ (section-projection ∙
        ((pullback-factor-β₁ top ▷ section) ∙ (comp-assoc section top-factor p) ⁻¹)))

    chosen-section : Section top-factor
    chosen-section = record { section = section ; section-law = section-triangle ⁻¹ }

    top-isPullback : IsPullback top
    top-isPullback = embedding-with-section top-factor top-factor-isEmbedding chosen-section
```
