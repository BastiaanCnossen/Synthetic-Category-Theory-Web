# Pushout squares

For `def:Pushout_Square`, `mappingOut` maps the specified square
contravariantly into a category `E`, giving a cone of mapping animae.
Its matching retains the two composition comparisons and the image of
the original commutativity isomorphism.

`IsPushout` asserts that this cone is a pullback cone for every `E`.
It is a property of the given square; this definition does not choose
a pushout for each span.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section08.PushoutSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 public hiding (squareCocone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P

mappingOut : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  Square u l r v → (E : CAT) → Cone (mapPre {D = E} u) (mapPre l) (Map D E)
mappingOut {u = u} {l} {r} {v} s E = record
  { left = mapPre r ; right = mapPre v
  ; match = (mapPre-comp l v) ⁻¹ ∙
      (mapPre-cong (Square.commute s) ∙ mapPre-comp u r) }

IsPushout : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  Square u l r v → Set (c ⊔ m)
IsPushout s = (E : CAT) → IsPullback (mappingOut s E)
```
