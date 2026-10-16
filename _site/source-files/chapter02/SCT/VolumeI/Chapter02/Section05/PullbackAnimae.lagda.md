# Pullbacks of animae and the core embedding

Recognition turns closure of groupoids under pullbacks into closure of animae,
even when the base category is arbitrary. This is
lem:Pullback_Of_Animae_Over_Category.

For prop:Groupoid_Core_Embeds_Into_C, use the first projection of the actual
self-pullback of the core inclusion. Its source and target are animae, so
mapping out of animae detects whether it is an equivalence. Every such test
is a projection of the mapped pullback square. The other cospan map is an
equivalence by the core universal property, so this projection is too.

The mapped square retains its chosen matching. Its first leg is the existing
postcomposition map by definition; no new comparison of cone matchings is
needed.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section05.PullbackAnimae where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section04.Core
  using (Core; coreInclusion; core-isAn; core-universal)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPost)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection using (post-tests-animae)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (Pullback; pullback₁)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (left-isEquiv-from-isPullback)
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks using (module MappingPullback)
open import SCT.VolumeI.Chapter01.Section06.Embeddings
  using (IsEmbedding; embedding-from-projection-isEquiv)
open import SCT.VolumeI.Chapter02.Section04.PullbackGroupoids using (pullback-isGroupoid)
open import SCT.VolumeI.Chapter02.Section05.Recognition using (anima-isGroupoid; groupoid-isAn)

module _ {Γ : Context} where
  pullback-of-animae : {X Y C : CAT Γ} (f : MAP X C) (g : MAP Y C)
    → isAn X → isAn Y → isAn (Pullback f g)
  pullback-of-animae f g ex ey = groupoid-isAn
    (pullback-isGroupoid f g (anima-isGroupoid ex) (anima-isGroupoid ey))

  coreInclusion-isEmbedding : (C : CAT Γ) → IsEmbedding (coreInclusion C)
  coreInclusion-isEmbedding C = embedding-from-projection-isEquiv i
    (post-tests-animae (pullback-of-animae i i (core-isAn C) (core-isAn C))
      (core-isAn C) projection tested)
    where
    i : MAP (Core C) C
    i = coreInclusion C

    projection : MAP (Pullback i i) (Core C)
    projection = pullback₁ {f = i} {g = i}

    tested : (X : CAT Γ) → isAn X → IsEquiv (mapPost {C = X} projection)
    tested X xAn = left-isEquiv-from-isPullback (core-universal X C xAn)
      (MappingPullback.square X i i) (MappingPullback.square-isPullback X i i)
```
