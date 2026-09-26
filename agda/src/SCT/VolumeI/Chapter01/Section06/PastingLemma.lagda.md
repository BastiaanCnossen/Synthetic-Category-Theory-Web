# The pasting lemma for pullback squares

When the right square is a pullback, the left square is a pullback exactly
when the pasted rectangle is. The comparison of factorization maps below
retains the matching isomorphism of that particular rectangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.Pasting.UniversalNestedPullbacks as Nested

module SCT.VolumeI.Chapter01.Section06.PastingLemma
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullbackLift-cong)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P

module Pasting {A B X Z Q : CAT} (f : MAP A B) (g : MAP B Z) (h : MAP X Z)
  (t : Cone g h Q) (et : IsPullback t) where

  module N = Nested.Nested 𝒯 P f g h t et
  module Paste = PasteCones f g t

  factorization : {T : CAT} (s : Cone f (Cone.left t) T) →
    (pullbackLift (Paste.flatten s)) =₁ (N.flatten ∘ pullbackLift s)
  factorization s = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse image) (pullbackLift-β (Paste.flatten s)))
    where
    image = coneIso-compose (Paste.flatten-iso (pullbackLift-β s))
      (coneIso-compose (Paste.flatten-pre (pullbackLift s) N.nestedCone)
      (coneIso-compose (coneIso-pre (pullbackLift s) (pullbackLift-β N.flatCone))
        (coneIso-inverse (conePre-assoc (pullbackLift s) N.flatten N.outerCone))))

  paste-isPullback : {T : CAT} (s : Cone f (Cone.left t) T) →
    IsPullback s → IsPullback (Paste.flatten s)
  paste-isPullback s es = equiv-transport ((factorization s) ⁻¹)
    (equiv-compose (pullbackLift s) N.flatten es N.flatten-isEquiv)

  cancel-isPullback : {T : CAT} (s : Cone f (Cone.left t) T) →
    IsPullback (Paste.flatten s) → IsPullback s
  cancel-isPullback s es = equiv-cancel-left (pullbackLift s) N.flatten N.flatten-isEquiv
    (equiv-transport (factorization s) es)
```
