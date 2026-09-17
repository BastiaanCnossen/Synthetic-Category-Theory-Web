# Pushout squares

For `def:Pushout_Square`, map the specified square contravariantly into
each category. The matching retains the two composition comparisons and
the image of the original commutativity isomorphism. Being a pushout is
the assertion that every such cone is a pullback cone.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section08.PushoutSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯 public
open import SCT.VolumeI.Chapter01.Section05.PullbackSquares 𝒯 P

mappingOut : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  Square u l r v → (E : CAT) → Cone (mapPre {D = E} u) (mapPre l) (Map D E)
mappingOut {u = u} {l} {r} {v} s E = record
  { left = mapPre r ; right = mapPre v
  ; match = invIso (mapPre-comp l v) ∙
      (mapPre-cong (Square.commute s) ∙ mapPre-comp u r) }

IsPushout : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  Square u l r v → Set (c ⊔ m)
IsPushout s = (E : CAT) → IsPullback (mappingOut s E)
```
