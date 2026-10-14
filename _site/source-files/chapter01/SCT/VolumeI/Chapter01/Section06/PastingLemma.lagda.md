# The pullback pasting lemma

The factor of the actual pasted cone compares to flattening after the factor
of the inner cone. This comparison retains the supplied cone's matching,
using its complete beta and pasting's restriction law. Since flattening is
an equivalence, the two universal properties are equivalent.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.PastingLemma where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose; equiv-transport; equiv-cancel-left)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.ConePasting
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks

module _ {Γ : Context} where
  module Pasting {A B X Z Q : CAT Γ} (f : MAP A B) (g : MAP B Z) (h : MAP X Z)
    (t : Cone g h Q) (e : IsPullback t) where
    module Nest = Nested f g h t e
    module Paste = PasteCones f g t

    factor-law : {S : CAT Γ} (s : Cone f (Cone.left t) S)
      → pullback-factor (Paste.paste s) =₁ (Nest.flatten ∘ pullback-factor s)
    factor-law s = pullback-factor-restrict (pullback-factor s) Nest.flat-cone ∙
      (pullback-factor-cong (cone-inverse (Paste.paste-restrict (pullback-factor s) Nest.nested-cone)) ∙
        pullback-factor-cong (cone-inverse (Paste.paste-identification (pullback-factor-β s))))

    paste-isPullback : {S : CAT Γ} (s : Cone f (Cone.left t) S)
      → IsPullback s → IsPullback (Paste.paste s)
    paste-isPullback s es = equiv-transport (factor-law s ⁻¹)
      (equiv-compose (pullback-factor s) Nest.flatten es Nest.flatten-isEquiv)

    unpaste-isPullback : {S : CAT Γ} (s : Cone f (Cone.left t) S)
      → IsPullback (Paste.paste s) → IsPullback s
    unpaste-isPullback s ep = equiv-cancel-left (pullback-factor s) Nest.flatten
      Nest.flatten-isEquiv (equiv-transport (factor-law s) ep)
```
