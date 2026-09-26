# Cancellation of pullback squares along embeddings

This proves `lem:Cancellation_Homotopy_Cartesian_Squars_With_Monomorphisms`.
The outer pullback supplies a section of the top comparison. Both the
comparison and the projection of the top pullback are embeddings, which
turns that section into an inverse. The construction keeps the matching
of the pasted rectangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCancellation
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P

module Cancellation {C D E D′ E′ C′ : CAT}
  (f : MAP C D) (g : MAP D E) (w : MAP E′ E)
  (bottom : Cone g w D′) (top : Cone f (Cone.left bottom) C′)
  (ev : IsEmbedding (Cone.left bottom)) (ew : IsEmbedding w)
  (outer-isPullback : IsPullback (PasteCones.flatten f g bottom top)) where

  module Paste = PasteCones f g bottom
  module Outer = UniversalCone (Paste.flatten top) outer-isPullback

  v = Cone.left bottom
  u = Cone.left top
  p = pullback₁ {f = f} {v}
  comparison = pullbackLift top

  projection-isEmbedding = chosen-base-change-embedding f v ev
  u-isEmbedding = base-change-embedding (Paste.flatten top) outer-isPullback ew
  comparison-isEmbedding = LeftCancellation.cancel comparison p projection-isEmbedding
    (embedding-cong ((pullbackLift-β₁ top) ⁻¹) u-isEmbedding)

  section : MAP (Pullback f v) C′
  section = Outer.factor (Paste.flatten (pullbackCone f v))

  section-projection : (u ∘ section) =₁ p
  section-projection = ConeIso.leftIso (Outer.factor-β (Paste.flatten (pullbackCone f v)))

  section-law : (comparison ∘ section) =₁ (id (Pullback f v))
  section-law = embedding-reflect p projection-isEmbedding _ _
    ((comp-unitʳ p) ⁻¹ ∙ (section-projection ∙
      ((pullbackLift-β₁ top ▷ section) ∙ (comp-assoc section comparison p) ⁻¹)))

  top-isPullback : IsPullback top
  top-isPullback = embedding-with-section comparison comparison-isEmbedding section section-law
```
